#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""护理知识图谱 · 构建与校验管线（build.py）

一句话：**读一份自包含的图谱 JSON → 校验 → 产出一个可独立拷走就用的静态目录**。

用法
----
    # 校验并重建（题目 = 参数：跑几遍即几份独立交付）
    python build.py --input data/<topicKey>-graph.json --out .

    # 只校验，不产出
    python build.py --input data/<topicKey>-graph.json --check-only

    # 从 5 列表（类型, 名称, 关系, 目标类型, 目标名称）转图谱数据骨架
    python build.py --from-triples 三元组.csv --out-graph 图谱数据.json

产出目录结构（每个题目一个，互不相干，单独拷走也能跑）
    <out>/<topicKey>-kg/
        index.html                     单页图谱（力导向图 + 检索 + 节点详情）
        lib/echarts.min.js             图形库（本地内置 · 断网可开）
        data/<topicKey>-graph.json     图谱数据（自包含）
        data/<topicKey>-graph.js       同一份数据的 JS 副本（避免 file:// 跨域）
        data/<topicKey>-triples.csv    5 列表原件（输入形态）
        data/search-terms.json         检索词清单（校验规则第 5 条的对照夹具）
        build.py                       本脚本（客户可自行重跑校验）
        README.md                      使用说明
        neo4j/                         可选 · Neo4j 导入包（非运行依赖）

判据
----
    9 条校验规则（与客户部自检脚本同一套判据、两份独立实现，互为交叉验证）
    + 附加检查（类型取值域 / 声明覆盖 / 5 列表对照）

纪律
----
    · 校验不通过 → 打印明细 + **非零退出**，不产出（`--force` 可强制产出）
    · 题目显示名只来自数据文件的 meta.topicName；脚本与页面模板里不出现任何题目名
    · 纯静态 · 零后端 · 全相对路径 · 双击 index.html 也能跑
"""

import argparse
import csv
import json
import os
import re
import shutil
import sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
TEMPLATE_INDEX = os.path.join(HERE, "template", "index.html")
ECHARTS_SRC = os.path.join(HERE, "lib", "echarts.min.js")

# --------------------------------------------------------------------------
# 判据常量（题目无关的领域常量，不是题目参数）
# --------------------------------------------------------------------------

# §八 规则 6 —— 「有主张」的节点类型：至少 1 条 evidence
TYPES_REQUIRING_EVIDENCE = {
    "SymptomSign", "ManagementPrinciple", "ManagementStrategy", "ManagementOutcome",
}

# §三 节点类型词汇表（两题共用；每份数据只许用自己那一组）
NODE_TYPE_DOMAIN = {
    "DiseaseCategory", "SymptomSign", "Exam", "ManagementPrinciple", "NursingTheory",
    "DiseaseEducation", "SymptomExperience", "ManagementStrategy", "ManagementOutcome",
    "SymptomCategory", "AssessmentTool", "RiskFactor", "PharmacologicalManagement",
    "NonPharmacologicalManagement", "SymptomStatus", "FunctionalStatus",
    "Reference", "CaseReport",
}
# §四 关系类型词汇表
RELATION_TYPE_DOMAIN = {
    "BELONGS_TO", "HAS_SYMPTOM", "DETECTED_BY", "MANAGED_BY", "EDUCATED_BY",
    "EXPERIENCED_AS", "ASSESSED_BY", "AT_RISK_BY", "TREATED_BY", "EFFECT_ON",
    "PART_OF_CASE", "SUPPORTED_BY",
}

# 分题允许的类型组 —— **从数据文件读**（data/type-groups.json）——
# ⛔ 代码里不写任何题目标识：题目 = 参数 ⇒ 类型组也是参数。
TOPIC_TYPE_GROUPS = {}


# --------------------------------------------------------------------------
# 工具函数
# --------------------------------------------------------------------------

def norm(s):
    """归一化：去首尾空格 · 折内空白 · 小写 · 去空格（中文与英文同一把尺子）"""
    if s is None:
        return ""
    s = str(s).strip().lower()
    s = re.sub(r"\s+", " ", s)
    return s.replace(" ", "")


def node_strings(node):
    """节点上可被检索命中的文本（规则第 5 条的判定范围）"""
    out = [node.get("name", "")]
    out.extend(node.get("aliases") or [])
    out.extend(node.get("tags") or [])
    out.append(node.get("summary", ""))
    return [norm(x) for x in out if x]


def evidence_types_of(nodes):
    """本图谱用到的全部证据类型字符串（evidence.type ∪ Reference 节点声明的类型）"""
    types = set()
    for n in nodes:
        for ev in n.get("evidence") or []:
            if isinstance(ev, dict) and ev.get("type"):
                types.add(str(ev["type"]).strip())
        if n.get("type") == "Reference":
            for ev in n.get("evidence") or []:
                if isinstance(ev, dict) and ev.get("type"):
                    types.add(str(ev["type"]).strip())
            for a in n.get("attrs") or []:
                if isinstance(a, dict) and a.get("k") in ("文献类型", "类型", "evidenceType"):
                    types.add(str(a.get("v", "")).strip())
    return {t for t in types if t}


def cite_ok(ev):
    """规则第 7 条 —— 文献四要素（作者 / 标题 / 期刊 / 年份）
    结构化写法优先；否则按分隔符切 cite 串，要求 ≥4 段且末段含年份。"""
    if not isinstance(ev, dict):
        return False, "evidence 项不是对象"
    if all(k in ev for k in ("author", "title", "journal")):
        year = str(ev.get("year", ""))
        ok = (bool(str(ev["author"]).strip()) and bool(str(ev["title"]).strip())
              and bool(str(ev["journal"]).strip()) and bool(re.search(r"(19|20)\d{2}", year)))
        return ok, ("结构化四要素齐全" if ok else "结构化字段有空缺或年份非法")
    cite = str(ev.get("cite", "") or "").strip()
    if not cite:
        return False, "cite 为空"
    parts = [p.strip() for p in re.split(r"[/,，;；|]", cite) if p.strip()]
    if len(parts) < 4:
        return False, "cite 段数 %d < 4（需作者/标题/期刊/年份）" % len(parts)
    if not re.search(r"(19|20)\d{2}", parts[-1]):
        return False, "cite 末段「%s」无年份" % parts[-1]
    if any(not p for p in parts[:3]):
        return False, "cite 前三段有空缺"
    return True, "四要素齐全"


def topic_key_of(path, data):
    """题目键：优先取文件名（<topicKey>-graph.json），与数据里的 meta.topicKey 交叉核对"""
    base = os.path.basename(path)
    m = re.match(r"^(topic[-_]?\d+)[-_]graph\.json$", base, re.I)
    from_name = m.group(1).lower().replace("_", "-") if m else None
    from_meta = str((data.get("meta") or {}).get("topicKey") or "").strip() or None
    return from_name or from_meta, from_name, from_meta


# --------------------------------------------------------------------------
# 校验器
# --------------------------------------------------------------------------

class Report(object):
    def __init__(self):
        self.items = []          # (rule_no, name, passed, detail)

    def add(self, no, name, passed, detail=""):
        self.items.append((no, name, bool(passed), detail))
        return passed

    @property
    def failed(self):
        return [i for i in self.items if not i[2]]

    def rule_failed(self, nos):
        return [i for i in self.items if not i[2] and i[0] in nos]


def load_terms(terms_path):
    with open(terms_path, "r", encoding="utf-8") as f:
        return json.load(f)


def topic_terms(doc, topic_key):
    """本主题的「主题词」—— 走节点文本通道（name / alias）"""
    return [t for t in doc["terms"]
            if t["topic"] == topic_key and "evidenceType" not in t["channels"]]


def evidence_terms(doc):
    """证据类型词 —— 走 evidence.type 通道，不走节点名匹配"""
    return [t for t in doc["terms"] if "evidenceType" in t["channels"]]


def check_terms_coverage(nodes, doc, topic_key):
    """规则第 5 条 —— 客户检索词覆盖

    返回 (uncovered_detail, ok, n_topic_terms, n_evidence_terms)"""
    ev_types = evidence_types_of(nodes)
    uncovered = []

    for t in topic_terms(doc, topic_key):
        key = norm(t["term"])
        exp_types = set(t.get("expectTypes") or [])
        hit = None
        for n in nodes:
            if exp_types and n.get("type") not in exp_types:
                continue
            for cand in node_strings(n):
                if key and (key == cand or key in cand or cand in key):
                    hit = "%s(%s)" % (n.get("name"), n.get("type"))
                    break
            if hit:
                break
        if not hit:
            uncovered.append("%s → 期望类型 %s" % (t["term"], "/".join(sorted(exp_types))))

    en_to_zh = (doc.get("evidenceTypeDomain") or {}).get("enToZh") or {}
    for t in evidence_terms(doc):
        zh = t["term"]
        if t.get("lang") == "en":
            zh = en_to_zh.get(t["term"], t["term"])
        if not any(norm(zh) == norm(x) for x in ev_types):
            uncovered.append("%s → evidence.type 缺「%s」" % (t["term"], zh))

    detail = ("未覆盖 %d 条：%s" % (len(uncovered), "; ".join(uncovered[:12]))) if uncovered else \
             ("本主题 %d 条主题词 + %d 类证据类型全部有落点"
              % (len(topic_terms(doc, topic_key)), len(evidence_terms(doc))))
    return uncovered, (not uncovered), detail


def check_file(path, topic_key, rep, doc, terms_source):
    """对一份数据文件跑规则 1/2/3/4/5/6/7/9 + 附加检查"""
    tag = os.path.basename(path)
    if not os.path.exists(path):
        rep.add("-", "文件存在", False, "%s 不存在" % path)
        return None
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception as e:
        rep.add("-", "JSON 可解析", False, "%s 解析失败：%s" % (tag, e))
        return None
    rep.add("-", "JSON 可解析（%s）" % tag, True, "")

    meta = data.get("meta") or {}
    nodes = data.get("nodes") or []
    edges = data.get("edges") or []
    node_types = data.get("nodeTypes") or []
    rel_types = data.get("relationTypes") or []

    # ---- 规则 1：节点 id 全局唯一
    ids = [n.get("id", "") for n in nodes]
    dup_ids = sorted(set([i for i in ids if ids.count(i) > 1]))
    rep.add(1, "节点 id 全局唯一（%s）" % tag, not dup_ids,
            ("重复 id：%s" % ", ".join(dup_ids)) if dup_ids else "节点 %d 个，id 无重复" % len(nodes))

    # ---- 规则 9：不混题（一份数据只能有一个 graph 取值，且等于本题）
    gvals = sorted(set([str(n.get("graph", "")) for n in nodes]))
    ok9 = (len(gvals) == 1 and gvals[0] == topic_key)
    rep.add(9, "不混题 · graph 唯一且等于 %s（%s）" % (topic_key, tag), ok9,
            "graph 取值 = %s" % (", ".join(gvals) if gvals else "（空）"))

    # ---- 规则 2：边的 source / target 都存在
    idset = set(ids)
    dangling = []
    for e in edges:
        for side in ("source", "target"):
            if e.get(side) not in idset:
                dangling.append("%s->%s[%s]" % (e.get("source"), e.get("target"), side))
    rep.add(2, "边的 source/target 都存在（%s）" % tag, not dangling,
            ("悬空边 %d 条：%s" % (len(dangling), "; ".join(dangling[:8]))) if dangling
            else "边 %d 条，端点全部命中" % len(edges))

    # ---- 规则 3：无重复边
    seen, dup_e = set(), []
    for e in edges:
        k = (e.get("source"), e.get("target"), e.get("type"))
        if k in seen:
            dup_e.append(k)
        seen.add(k)
    rep.add(3, "无重复边（%s）" % tag, not dup_e,
            ("重复边 %d 条" % len(dup_e)) if dup_e else "无重复边")

    # ---- 规则 4：节点 (type, name) 唯一
    pairs = [(n.get("type"), n.get("name")) for n in nodes]
    dup_p = sorted(set([k for k in pairs if pairs.count(k) > 1]))
    rep.add(4, "节点 (type, name) 唯一（%s）" % tag, not dup_p,
            ("重复 (type,name)：%s" % "; ".join("%s/%s" % k for k in dup_p[:8])) if dup_p
            else "无重复节点")

    # ---- 规则 5：客户检索词覆盖
    if doc is None:
        rep.add(5, "客户检索词覆盖（%s）" % tag, True,
                "⚠ 跳过 —— 未找到检索词夹具（search-terms.json）：本次未做覆盖检查")
    else:
        _, ok5, detail5 = check_terms_coverage(nodes, doc, topic_key)
        rep.add(5, "客户检索词覆盖（%s）" % tag, ok5, detail5)

    # ---- 规则 6：证据完整性
    missing_ev = []
    for n in nodes:
        if n.get("type") in TYPES_REQUIRING_EVIDENCE:
            if not (n.get("evidence") or []):
                missing_ev.append("%s(%s)" % (n.get("name"), n.get("type")))
    rep.add(6, "证据完整性（%s）" % tag, not missing_ev,
            ("有主张但无 evidence %d 个：%s" % (len(missing_ev), "; ".join(missing_ev[:10])))
            if missing_ev else "有主张的节点全部带 evidence")

    # ---- 规则 7：evidence.cite 四要素
    bad_cite, ev_total = [], 0
    for n in nodes:
        for ev in n.get("evidence") or []:
            ev_total += 1
            ok, why = cite_ok(ev)
            if not ok:
                bad_cite.append("%s: %s" % (n.get("name"), why))
    rep.add(7, "evidence.cite 四要素（%s）" % tag, not bad_cite,
            ("不合规 %d 条：%s" % (len(bad_cite), "; ".join(bad_cite[:8]))) if bad_cite
            else "%d 条 evidence 全部含作者/标题/期刊/年份" % ev_total)

    # ---- 附加：类型取值域 / 声明覆盖 / 主题一致
    bad_types = sorted(set([str(n.get("type")) for n in nodes]) - NODE_TYPE_DOMAIN)
    rep.add("附A", "节点类型取值域合法（%s）" % tag, not bad_types,
            ("越界类型：%s" % ", ".join(bad_types)) if bad_types else "全部在类型词汇表内")

    allowed = TOPIC_TYPE_GROUPS.get(topic_key)
    if allowed is None:
        rep.add("附B", "只用本主题允许的类型组（%s）" % tag, True,
                "⚠ 未登记该主题的类型组 —— 不做主题类型组限定")
    else:
        off_topic = sorted(set([str(n.get("type")) for n in nodes]) - allowed)
        rep.add("附B", "只用本主题允许的类型组（%s）" % tag, not off_topic,
                ("跨主题类型：%s" % ", ".join(off_topic)) if off_topic else "类型组与主题一致")

    bad_rel = sorted(set([str(e.get("type")) for e in edges]) - RELATION_TYPE_DOMAIN)
    rep.add("附C", "关系类型取值域合法（%s）" % tag, not bad_rel,
            ("越界关系类型：%s" % ", ".join(bad_rel)) if bad_rel else "全部在关系类型词汇表内")

    declared_nodes = set([t.get("key") for t in node_types if isinstance(t, dict)])
    used_nodes = set([str(n.get("type")) for n in nodes])
    undeclared = sorted(used_nodes - declared_nodes)
    rep.add("附D", "nodeTypes 声明覆盖实用类型（%s）" % tag, not undeclared,
            ("未声明：%s" % ", ".join(undeclared)) if undeclared
            else "声明 %d 类，覆盖实用 %d 类" % (len(declared_nodes), len(used_nodes)))

    declared_rel = set([t.get("key") for t in rel_types if isinstance(t, dict)])
    used_rel = set([str(e.get("type")) for e in edges])
    undeclared_r = sorted(used_rel - declared_rel)
    rep.add("附E", "relationTypes 声明覆盖实用类型（%s）" % tag, not undeclared_r,
            ("未声明：%s" % ", ".join(undeclared_r)) if undeclared_r
            else "声明 %d 类，覆盖实用 %d 类" % (len(declared_rel), len(used_rel)))

    # ---- 附加：边的 type(key) ↔ label(中文关系名) 必须与 relationTypes 声明指向同一条
    #      （否则前端图例会画出与关系语义不符的名称 —— 旧判据只比 CSV↔label，查不出来）
    rel_by_key = dict([(t.get("key"), t) for t in rel_types if isinstance(t, dict)])
    label_by_key = dict([(str(t.get("label")), str(t.get("key")))
                         for t in rel_types if isinstance(t, dict)])
    from collections import Counter
    dup_labels = sorted([l for l, c in Counter(
        [str(t.get("label")) for t in rel_types if isinstance(t, dict)]).items() if c > 1])
    label_mismatch = []
    for e in edges:
        k, lb = str(e.get("type", "")), str(e.get("label", ""))
        decl = rel_by_key.get(k)
        if decl is None:
            continue                      # 越界 type 已在「关系类型取值域合法」报过
        if str(decl.get("label", "")) != lb:
            label_mismatch.append("%s 的 label「%s」应为「%s」" % (k, lb, decl.get("label")))
    rep.add("附F", "边 type↔label 与 relationTypes 一致（%s）" % tag,
            not label_mismatch and not dup_labels,
            ("；".join(label_mismatch[:8]) if label_mismatch
             else ("relationTypes 有重复 label：%s" % ", ".join(dup_labels) if dup_labels
                   else "%d 条边的 type↔label 全部与声明一致" % len(edges))))

    # ---- 附加：meta 自洽（题目键 · 显示名）
    meta_topic = str(meta.get("topicKey") or "").strip()
    rep.add("附K", "meta 自洽（%s）" % tag,
            (not meta_topic or meta_topic == topic_key) and bool(meta.get("topicName")),
            "meta.topicKey=%s · meta.topicName=%s" % (meta_topic or "（缺）", meta.get("topicName") or "（缺）"))

    # ---- 附加：5 列表逐行对照（仅当同目录存在该表时；这是客户部的对照件，只读不改）
    csv_path = os.path.join(os.path.dirname(path),
                            os.path.basename(path).replace("-graph.json", "-triples.csv"))
    if os.path.exists(csv_path):
        with open(csv_path, "r", encoding="utf-8-sig", newline="") as f:
            rows = [r for r in csv.reader(f) if r and any(c.strip() for c in r)]
        if rows and rows[0] and rows[0][0].strip() in ("sub_type", "类型", "src_type"):
            body = rows[1:]
        else:
            body = rows
        bad_rows = [i + 2 for i, r in enumerate(body) if len(r) < 5 or any(not str(c).strip() for c in r[:5])]
        rep.add("附G", "5 列表每行 5 列且非空（%s）" % os.path.basename(csv_path), not bad_rows,
                ("空列行：%s" % bad_rows[:10]) if bad_rows else "%d 行，列齐全" % len(body))
        rep.add("附H", "5 列表行数 = 边数（%s）" % os.path.basename(csv_path), len(body) == len(edges),
                "表 %d 行 vs 边 %d 条" % (len(body), len(edges)))

        by_id = dict([(n.get("id"), n) for n in nodes])
        edge_tuples, dangling_n = [], 0
        for e in edges:
            s, t = by_id.get(e.get("source")), by_id.get(e.get("target"))
            if not s or not t:
                dangling_n += 1
                continue
            edge_tuples.append((str(s.get("type", "")), str(s.get("name", "")),
                                str(e.get("label", "")), str(t.get("type", "")), str(t.get("name", ""))))
        csv_tuples = [tuple(str(c).strip() for c in r[:5]) for r in body if len(r) >= 5]
        diff = []
        if dangling_n:
            diff.append("有 %d 条边引用了不存在的节点（规则 2 已报）" % dangling_n)
        miss = Counter(edge_tuples) - Counter(csv_tuples)
        extra = Counter(csv_tuples) - Counter(edge_tuples)
        for t_, n_ in sorted(miss.items())[:5]:
            diff.append("edges 有而 CSV 无 ×%d：%s" % (n_, " | ".join(t_)))
        for t_, n_ in sorted(extra.items())[:5]:
            diff.append("CSV 有而 edges 无 ×%d：%s" % (n_, " | ".join(t_)))
        rep.add("附I", "5 列表逐行对应边内容（%s）" % os.path.basename(csv_path), not diff,
                ("；".join(diff) if diff else "%d 行逐条对上边（类型 / 名称 / 关系名）" % len(csv_tuples)))

        csv_rel_labels = sorted(set([str(r[2]).strip() for r in body if len(r) >= 5]))
        unknown_rel = [l for l in csv_rel_labels if l not in label_by_key]
        rep.add("附J", "5 列表关系名在关系类型词表内（%s）" % os.path.basename(csv_path), not unknown_rel,
                ("词表外关系名：%s" % ", ".join(unknown_rel[:8])) if unknown_rel
                else "%d 个关系名全部在关系类型词表内" % len(csv_rel_labels))
    else:
        rep.add("附G", "5 列表存在（%s）" % os.path.basename(csv_path), True,
                "⚠ 同目录无 5 列表 —— 跳过对照（该对照属客户部自检职责 · §2.2 回执第 4 条）")

    return data


def check_same_criteria(datas, rep):
    """规则 8 —— 两份走同一套判据（节点类型 / 关系类型词汇表一致）"""
    if len(datas) < 2:
        rep.add(8, "两份走同一套判据（类型词汇表一致）", True,
                "⚠ 本次只跑 %d 份数据 —— 跨题一致性检查不适用" % len(datas))
        return
    sets = {}
    for tk, d in datas.items():
        sets[tk] = (
            sorted(set([t.get("key") for t in (d.get("nodeTypes") or []) if isinstance(t, dict)])),
            sorted(set([t.get("key") for t in (d.get("relationTypes") or []) if isinstance(t, dict)])),
        )
    keys = sorted(sets.keys())
    same = all(sets[keys[0]][i] == sets[k][i] for k in keys[1:] for i in (0, 1))
    detail = "节点类型 %d 类 + 关系类型 %d 类，各题一致" % (len(sets[keys[0]][0]), len(sets[keys[0]][1]))
    if not same:
        detail = "；".join(
            "%s 节点类型差异：仅 %s 有 %s" % (keys[0], k, sorted(set(sets[keys[0]][0]) ^ set(sets[k][0])))
            for k in keys[1:])
    rep.add(8, "两份走同一套判据（类型词汇表一致）", same, detail)


# --------------------------------------------------------------------------
# 产出
# --------------------------------------------------------------------------

def write_neo4j_pack(out_dir, data):
    """Neo4j 导入包（可选件 · 非运行依赖）

    按缺陷清单重写：MERGE 而非 CREATE · 参数化 · 不无条件清库 · 不做笛卡尔积匹配 ·
    按 (label, name) 去重 · 导入可重复执行。"""
    neo = os.path.join(out_dir, "neo4j")
    if not os.path.isdir(neo):
        os.makedirs(neo)

    nodes = data.get("nodes") or []
    edges = data.get("edges") or []
    by_id = dict([(n.get("id"), n) for n in nodes])

    # 节点：按 (label, name) 去重
    seen = set()
    # 写 **不带 BOM**（utf-8）：Neo4j 的 LOAD CSV 不剥 BOM → 首列列名会变成 "﻿id"
    with open(os.path.join(neo, "nodes.csv"), "w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["id", "label", "name", "summary", "tags", "evidence_count"])
        for n in nodes:
            label = str(n.get("type") or "Entity")
            name = str(n.get("name") or "")
            key = (label, name)
            if key in seen:
                continue
            seen.add(key)
            w.writerow([
                n.get("id", ""), label, name, n.get("summary", "") or "",
                " ".join(n.get("tags") or []), len(n.get("evidence") or []),
            ])

    with open(os.path.join(neo, "edges.csv"), "w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["source_id", "source_label", "source_name", "type",
                    "relationship_label", "target_id", "target_label", "target_name"])
        for e in edges:
            s, t = by_id.get(e.get("source")), by_id.get(e.get("target"))
            if not s or not t:
                continue
            w.writerow([
                s.get("id", ""), str(s.get("type") or ""), str(s.get("name") or ""),
                str(e.get("type") or ""), str(e.get("label") or ""),
                t.get("id", ""), str(t.get("type") or ""), str(t.get("name") or ""),
            ])

    cypher = """// ===========================================================================
// Neo4j 导入包（可选件 · 不是本页面的运行依赖 —— 页面是纯静态的）
//
// 用法
//   1) 把 nodes.csv / edges.csv 放进 Neo4j 的 import 目录；
//   2) 在 Neo4j Browser 里执行本文件（:param 指定文件位置）。
//
// 本文件已按下列约束重写：
//   · 只 MERGE 不 CREATE —— 重复执行不会产生重复节点/关系
//   · 唯一约束 —— 节点按 (label, name)、关系按 (type, source_name, target_name)
//   · 参数化 —— 文件位置走 :param，字段走行变量，不拼字符串
//   · 不清库 —— 不含任何无条件 DELETE / DETACH DELETE
//   · 不做笛卡尔积匹配 —— 两端各自按 (label, name) 精确匹配
//   · 不含任何连接串 / 账号 / 口令
// ===========================================================================

:param nodeFile => 'file:///nodes.csv';
:param edgeFile => 'file:///edges.csv';

// ---- 唯一约束（幂等：已存在则跳过）----
CREATE CONSTRAINT kg_node_unique IF NOT EXISTS
  FOR (n:KGNode) REQUIRE (n.label, n.name) IS UNIQUE;

CREATE CONSTRAINT kg_rel_unique IF NOT EXISTS
  FOR ()-[r:HAS_REL]-() REQUIRE (r.type, r.source_name, r.target_name) IS UNIQUE;

// ---- 节点 ----
LOAD CSV WITH HEADERS FROM $nodeFile AS row
MERGE (n:KGNode {label: row.label, name: row.name})
SET n.id = row.id,
    n.summary = row.summary,
    n.tags = row.tags,
    n.evidence_count = toInteger(row.evidence_count);

// ---- 关系 ----
LOAD CSV WITH HEADERS FROM $edgeFile AS row
MATCH (s:KGNode {label: row.source_label, name: row.source_name})
MATCH (t:KGNode {label: row.target_label, name: row.target_name})
MERGE (s)-[r:HAS_REL {type: row.type,
                      source_name: row.source_name,
                      target_name: row.target_name}]->(t)
SET r.label = row.relationship_label,
    r.source_id = row.source_id,
    r.target_id = row.target_id;

// ---- 自检：数量对不上就是导入没跑全（对比 build.py 打印的节点数 / 边数）----
MATCH (n:KGNode) RETURN count(n) AS nodes;
MATCH ()-[r:HAS_REL]->() RETURN count(r) AS relations;
"""
    with open(os.path.join(neo, "import.cypher"), "w", encoding="utf-8", newline="\n") as f:
        f.write(cypher)


README_TMPL = """# {topic_name} · 知识图谱（静态交付包）

> 本目录是**一份可独立拷走就用的完整交付**：前端 + 数据 + 构建脚本都在里面，
> 单独拷走这一份，照样能打开、能检索。**纯静态 · 零后端 · 全部相对路径。**

## 一、怎么打开

| 方式 | 做法 |
|---|---|
| 本地看 | 双击 `index.html`（数据走 `data/*.js` 副本，浏览器本地打开不受跨域限制）|
| 上线 | 整个目录原样丢进任意静态托管（对象存储 / CDN / 静态站点），无需服务端配置 |

⛔ 页面**不请求任何后端接口**，也**不连数据库**——数据随目录发布，检索在浏览器里算。

## 二、目录结构

```
{topic_key}-kg/
├── index.html                     单页图谱（力导向图 + 图例 + 检索 + 节点详情）
├── lib/echarts.min.js             图形库（本地内置 · 断网也能打开）
├── data/{topic_key}-graph.json     图谱数据（自包含：类型定义 + 节点 + 边 + 文献出处）
├── data/{topic_key}-graph.js       同一份数据的 JS 副本（页面直接读它）
├── data/{topic_key}-triples.csv    5 列表原件（输入形态 · 可直接重新生成图谱数据）
├── data/search-terms.json         检索词清单（校验规则第 5 条的对照夹具）
├── build.py                       构建脚本（校验 + 重新生成）
├── README.md                      本文件
└── neo4j/                         可选 · Neo4j 导入包（非运行依赖）
    ├── nodes.csv
    ├── edges.csv
    └── import.cypher
```

## 三、怎么用 build.py

```bash
# 重新校验 + 重建（Python 3.8+，只用标准库）
python build.py --input data/{topic_key}-graph.json --out .

# 只校验，不产出
python build.py --input data/{topic_key}-graph.json --check-only

# 从 5 列表转图谱数据骨架（类型, 名称, 关系, 目标类型, 目标名称）
python build.py --from-triples 三元组.csv --out-graph 图谱数据.json
```

**校验不通过 → 打印明细 + 非零退出**（不静默、不产出半成品）。判据 9 条：

1. 节点 id 全局唯一
2. 边的 source / target 都存在
3. 无重复边（source + target + type）
4. 节点 (type, name) 唯一
5. 客户检索词覆盖（对照 `data/search-terms.json`）
6. 有主张的节点类型至少 1 条文献
7. 文献四要素齐全（作者 / 标题 / 期刊 / 年份）
8. 多份数据走同一套判据（类型词汇表一致）
9. 不混题（一份数据只有一个 `graph` 取值）

## 四、检索怎么用

| 输入 | 命中通道 |
|---|---|
| 节点名称 / 别名 / 简介 / 属性 | 节点文本通道（大小写不敏感 · 首尾空格忽略 · 双向子串）|
| 文献类型（指南 / 共识 / 系统评价 / Meta 分析 …）| 文献类型通道 —— 命中**引用了该类型文献**的节点 |

英文文献类型词（`guidelines` / `systematic reviews` / `meta analysis`）与中文类型词命中**同一批节点**。
⛔ 节点级同义词（英文写法 / 旧称 / 错字写法）一律写在数据文件的 `aliases` 里，不写死在代码里。

## 五、数据说明

- 数据文件自包含：`meta`（题目元数据）· `nodeTypes`（类型定义，**样式随数据走**）·
  `relationTypes`（关系定义）· `nodes` · `edges`。
- 节点类型未在 `nodeTypes` 里声明时，页面走兜底样式，不会白屏。
- 文献出处挂在节点的 `evidence` 上，页面详情面板里逐条显示作者 / 标题 / 期刊 / 年份。
- ⛔ **没有真实出处的节点不要写进图谱** —— 校验脚本会按缺失项报出来。

## 六、Neo4j 导入包（可选）

`neo4j/` 里是给**想自己入库**的人准备的：把两个 csv 放进 Neo4j 的 import 目录，
在 Browser 里执行 `import.cypher`。它是**可选件**，页面本身不需要数据库。

---
生成于 {generated_at}
"""


def copy_if_different(src, dst):
    """拷贝 —— 源与目标是同一个文件时跳过（就地重建会撞上）"""
    if not os.path.exists(src):
        return False
    if os.path.abspath(src) == os.path.abspath(dst):
        return False
    shutil.copyfile(src, dst)
    return True


def build_one(topic_key, data, src_path, out_root, rep, terms_source):
    """产出 <out_root>/<topic_key>-kg/

    ⛔ 若 out_root 本身就是该题目的交付目录（就地重建），**直接写在里面** ——
       否则会套出 <topicKey>-kg/<topicKey>-kg/ 的嵌套目录。"""
    base = os.path.basename(os.path.abspath(out_root).rstrip("/\\"))
    if base == "%s-kg" % topic_key:
        out_dir = out_root
    else:
        out_dir = os.path.join(out_root, "%s-kg" % topic_key)
    data_dir = os.path.join(out_dir, "data")
    lib_dir = os.path.join(out_dir, "lib")
    for d in (out_dir, data_dir, lib_dir):
        if not os.path.isdir(d):
            os.makedirs(d)

    # 1 · 数据（原件照抄，不改客户部交付的文件）
    json_dst = os.path.join(data_dir, "%s-graph.json" % topic_key)
    copy_if_different(src_path, json_dst)

    # 2 · JS 副本（页面读它 → file:// 不撞跨域）
    with open(json_dst, "r", encoding="utf-8") as f:
        payload = f.read()
    with open(os.path.join(data_dir, "%s-graph.js" % topic_key), "w",
              encoding="utf-8", newline="\n") as f:
        f.write("window.KG_GRAPH = %s;\n" % payload)

    # 3 · 检索词夹具（随包提供，客户可自行重跑覆盖检查）
    if terms_source:
        copy_if_different(terms_source, os.path.join(data_dir, "search-terms.json"))

    # 3b · 5 列表（输入形态的原件：随包提供 → 客户可重跑对照，也可直接 --from-triples 重建）
    csv_src = os.path.join(os.path.dirname(os.path.abspath(src_path)),
                           os.path.basename(src_path).replace("-graph.json", "-triples.csv"))
    copy_if_different(csv_src, os.path.join(data_dir, "%s-triples.csv" % topic_key))

    # 3c · 分题类型组对照表（随包提供 → 校验脚本在交付目录里也能跑完整套判据）
    groups_src = None
    for c in (os.path.join(os.path.dirname(os.path.abspath(src_path)), "type-groups.json"),
              os.path.join(HERE, "data", "type-groups.json"),
              os.path.join(os.path.dirname(HERE), "data", "type-groups.json")):
        if os.path.exists(c):
            groups_src = c
            break
    if groups_src:
        copy_if_different(groups_src, os.path.join(data_dir, "type-groups.json"))

    # 4 · 图形库
    copy_if_different(ECHARTS_SRC, os.path.join(lib_dir, "echarts.min.js"))

    # 5 · 页面（模板在脚本旁边时重建；交付目录里没有模板就保留现有页面）
    index_dst = os.path.join(out_dir, "index.html")
    if os.path.exists(TEMPLATE_INDEX):
        with open(TEMPLATE_INDEX, "r", encoding="utf-8") as f:
            tpl = f.read()
        with open(index_dst, "w", encoding="utf-8", newline="\n") as f:
            f.write(tpl.replace("{{TOPIC_KEY}}", topic_key))
    elif not os.path.exists(index_dst):
        raise RuntimeError("找不到页面模板，且目录里没有现成的 index.html：%s" % out_dir)

    # 6 · 构建脚本（把自己带进交付目录，客户可自行重跑）
    copy_if_different(os.path.abspath(__file__), os.path.join(out_dir, "build.py"))

    # 7 · 说明
    meta = data.get("meta") or {}
    with open(os.path.join(out_dir, "README.md"), "w", encoding="utf-8", newline="\n") as f:
        f.write(README_TMPL.format(
            topic_name=meta.get("topicName") or topic_key,
            topic_key=topic_key,
            generated_at=datetime.now().strftime("%Y-%m-%d %H:%M")))

    # 8 · Neo4j 导入包（可选件）
    write_neo4j_pack(out_dir, data)

    rep.add("-", "产出目录（%s）" % tag_of(src_path), True, out_dir)
    return out_dir


def tag_of(path):
    return os.path.basename(path)


# --------------------------------------------------------------------------
# 5 列表 → 图谱数据骨架
# --------------------------------------------------------------------------

def triples_to_graph(csv_path, out_graph):
    """把 5 列表（类型, 名称, 关系, 目标类型, 目标名称）转成图谱数据骨架

    ⚠️ 产出的只是**骨架**：节点与关系齐了，别名 / 简介 / 文献出处需要另行补齐，
       补齐后再跑 build.py 的校验（缺什么会逐条报出来）。"""
    with open(csv_path, "r", encoding="utf-8-sig", newline="") as f:
        rows = [r for r in csv.reader(f) if r and any(c.strip() for c in r)]
    if not rows:
        raise SystemExit("5 列表是空的：%s" % csv_path)
    header = rows[0]
    if header and header[0].strip() in ("sub_type", "类型", "src_type"):
        body = rows[1:]
    else:
        body = rows

    nodes, edges = [], []
    index = {}

    def node_of(t, n):
        key = (t, n)
        if key not in index:
            nid = "n%03d" % (len(nodes) + 1)
            index[key] = nid
            nodes.append({
                "id": nid, "name": n, "type": t,
                "tags": [], "aliases": [], "summary": "",
                "attrs": [], "evidence": [],
            })
        return index[key]

    for r in body:
        if len(r) < 5:
            continue
        st, sn, rel, ot, on = [str(c).strip() for c in r[:5]]
        if not (st and sn and rel and ot and on):
            continue
        edges.append({
            "source": node_of(st, sn), "target": node_of(ot, on),
            "type": rel.upper().replace(" ", "_"), "label": rel,
        })

    graph = {
        "meta": {
            "topicKey": "",
            "topicName": "",
            "subtitle": "由 5 列表转换生成的骨架（待补别名 / 简介 / 文献出处）",
            "generatedAt": datetime.now().strftime("%Y-%m-%d"),
        },
        "nodeTypes": [], "relationTypes": [],
        "nodes": nodes, "edges": edges,
    }
    with open(out_graph, "w", encoding="utf-8", newline="\n") as f:
        json.dump(graph, f, ensure_ascii=False, indent=1)
    print("已写出图谱数据骨架：%s（节点 %d · 边 %d）" % (out_graph, len(nodes), len(edges)))
    print("⛔ 别名 / 简介 / 文献出处需另行补齐 —— 没有真实出处的节点不要进图谱。")


# --------------------------------------------------------------------------
# 入口
# --------------------------------------------------------------------------

def find_terms(paths, explicit):
    """找检索词夹具：--terms → 输入文件同目录 → 脚本旁的 data/ → 上一级的 data/"""
    if explicit:
        return explicit if os.path.exists(explicit) else None
    cands = []
    for p in paths:
        cands.append(os.path.join(os.path.dirname(os.path.abspath(p)), "search-terms.json"))
    cands.append(os.path.join(HERE, "data", "search-terms.json"))
    cands.append(os.path.join(os.path.dirname(HERE), "data", "search-terms.json"))
    for c in cands:
        if os.path.exists(c):
            return c
    return None


def load_type_groups(paths, explicit):
    """读分题允许的类型组（数据文件）—— 代码里不写题目标识"""
    global TOPIC_TYPE_GROUPS
    cands = []
    if explicit:
        cands.append(explicit)
    for p in paths:
        cands.append(os.path.join(os.path.dirname(os.path.abspath(p)), "type-groups.json"))
    cands.append(os.path.join(HERE, "data", "type-groups.json"))
    cands.append(os.path.join(os.path.dirname(HERE), "data", "type-groups.json"))
    for c in cands:
        if not os.path.exists(c):
            continue
        try:
            with open(c, "r", encoding="utf-8") as f:
                doc = json.load(f)
            groups = doc.get("groups") or {}
            TOPIC_TYPE_GROUPS = dict((k, set(v)) for k, v in groups.items())
            return c
        except Exception as e:
            print("⚠ 类型组表读取失败（%s）：%s —— 该项检查本次跳过" % (c, e))
    return None


def main(argv):
    ap = argparse.ArgumentParser(description="知识图谱构建与校验管线")
    ap.add_argument("--input", action="append", default=[],
                    help="图谱数据 JSON（可多次；每份产出一个独立目录）")
    ap.add_argument("--out", default=".", help="产出根目录（默认当前目录）")
    ap.add_argument("--terms", default=None, help="检索词夹具 search-terms.json")
    ap.add_argument("--type-groups", default=None, help="分题类型组对照表 type-groups.json")
    ap.add_argument("--check-only", action="store_true", help="只校验，不产出")
    ap.add_argument("--no-neo4j", action="store_true", help="不产出 Neo4j 导入包")
    ap.add_argument("--force", action="store_true", help="校验不过也产出（默认不产出）")
    ap.add_argument("--from-triples", default=None, help="从 5 列表转图谱数据骨架")
    ap.add_argument("--out-graph", default=None, help="--from-triples 的输出路径")
    ap.add_argument("--json", action="store_true", help="以 JSON 输出逐条判定（供交叉验证）")
    args = ap.parse_args(argv[1:])

    if args.from_triples:
        if not args.out_graph:
            print("⛔ --from-triples 需要同时给 --out-graph")
            return 2
        triples_to_graph(args.from_triples, args.out_graph)
        return 0

    inputs = list(args.input)
    if not inputs:
        # 默认：当前目录 data/ 下所有 <key>-graph.json
        data_dir = os.path.join(os.getcwd(), "data")
        if os.path.isdir(data_dir):
            for fn in sorted(os.listdir(data_dir)):
                if fn.endswith("-graph.json"):
                    inputs.append(os.path.join(data_dir, fn))
    if not inputs:
        print("⛔ 没有输入：请用 --input 指定图谱数据 JSON")
        return 2

    terms_source = find_terms(inputs, args.terms)
    doc = None
    if terms_source:
        try:
            doc = load_terms(terms_source)
        except Exception as e:
            print("⛔ 检索词夹具读取失败：%s（%s）" % (terms_source, e))
            return 2
    else:
        print("⚠ 未找到检索词夹具 search-terms.json —— 规则第 5 条（检索词覆盖）本次跳过。")

    groups_source = load_type_groups(inputs, args.type_groups)
    if groups_source:
        print("类型组对照表：%s" % groups_source)
    else:
        print("⚠ 未找到类型组对照表 type-groups.json —— 「只用本主题允许的类型组」本次跳过。")

    rep = Report()
    datas, topic_of = {}, {}
    for p in inputs:
        if not os.path.exists(p):
            print("⛔ 输入文件不存在：%s" % p)
            return 2
        try:
            with open(p, "r", encoding="utf-8") as f:
                probe = json.load(f)
        except Exception as e:
            print("⛔ 输入文件解析失败：%s（%s）" % (p, e))
            return 2
        tk, from_name, from_meta = topic_key_of(p, probe)
        if not tk:
            print("⛔ 无法判定题目键（文件名与 meta.topicKey 都没有）：%s" % p)
            return 2
        if from_name and from_meta and from_name != from_meta:
            rep.add("附F", "文件名与 meta.topicKey 一致（%s）" % tag_of(p), False,
                    "文件名判定=%s · meta.topicKey=%s" % (from_name, from_meta))
        topic_of[tk] = p
        datas[tk] = check_file(p, tk, rep, doc, terms_source)

    check_same_criteria(datas, rep)

    # ---- JSON 输出（供跨实现交叉验证：逐条比 verdict）
    if args.json:
        print(json.dumps({
            "passed": not rep.failed,
            "items": [{"rule": n, "name": nm, "passed": p, "detail": d}
                      for n, nm, p, d in rep.items],
        }, ensure_ascii=False, indent=2))
        return 0 if not rep.failed else 1

    # ---- 报告
    print("=" * 78)
    print("知识图谱构建与校验 —— %d 份数据 · 同一套判据" % len(inputs))
    if terms_source:
        print("检索词夹具：%s" % terms_source)
    print("=" * 78)
    for n, nm, p, d in rep.items:
        print("[%s] %-4s %s" % ("PASS" if p else "FAIL", n, nm))
        if d:
            print("       %s" % d)
    nf = len(rep.failed)
    print("-" * 78)
    print("合计 %d 项检查 · 通过 %d · 不通过 %d" % (len(rep.items), len(rep.items) - nf, nf))
    if nf:
        print("⛔ 不通过项：")
        for n, nm, p, d in rep.failed:
            print("   · %s —— %s\n     %s" % (n, nm, d))

    if nf and not args.force:
        print("\n⛔ 校验未通过 —— 不产出（要强制产出请加 --force）")
        return 1

    if args.check_only:
        print("\n✅ 只校验模式 —— 未产出任何文件")
        return 0 if nf == 0 else 1

    # ---- 产出
    out_root = os.path.abspath(args.out)
    if not os.path.isdir(out_root):
        os.makedirs(out_root)
    print("\n产出：")
    for tk, p in topic_of.items():
        d = datas.get(tk)
        if d is None:
            continue
        out_dir = build_one(tk, d, p, out_root, rep, terms_source)
        print("   %s" % out_dir)
    print("\n✅ 完成")
    return 0 if nf == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
