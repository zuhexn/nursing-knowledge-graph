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
        index.html                     单页图谱（卡片流 + 全景图 + 检索 + 节点详情）
        lib/echarts.min.js             图形库（本地内置 · 断网可开）
        data/<topicKey>-graph.json     图谱数据（自包含）
        data/<topicKey>-graph.js       同一份数据的 JS 副本（避免 file:// 跨域）
        data/<topicKey>-triples.csv    5 列表原件（输入形态）
        data/<topicKey>-triples.js     5 列表的 JS 副本（三元组页直接读它）
        triples.html                   三元组表页（可直接看 · 可搜索 · 可下 CSV）
        data/<topicKey>-patient.json   患者层数据（可选：导语 + 免责 + 就医警示）
        data/<topicKey>-patient.js     同一份数据的 JS 副本（页面直接读它）
        data/search-terms.json         检索词清单（校验规则第 5 条的对照夹具）
        build.py                       本脚本（客户可自行重跑校验）
        README.md                      使用说明
        neo4j/                         可选 · Neo4j 导入包（非运行依赖）

判据
----
    9 条校验规则（与客户部自检脚本同一套判据、两份独立实现，互为交叉验证）
    + 附加检查（类型取值域 / 声明覆盖 / 5 列表对照）
    + 患者层检查（P 系列：就医警示必须挂在图谱里带文献出处的节点上）

结构闸门（写盘前 + 写盘后各跑一次）
----
    S · 静态结构（标签配平 / 裸标签字面量 / 必备锚点 / 占位符全替换）
    J · JS 语法（node --check 内联脚本）
    R · 首屏渲染（playwright 1440×900 真跑一次）
    M · 移动端列表视图（playwright 390×844 真跑一次）

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
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime
from html.parser import HTMLParser


# --- 控制台编码兜底（中文 Windows 默认 GBK）--------------------------------
# 本脚本的输出带 ⛔ / ✅ / ⚠ / ⇒ 等符号；GBK 编不出这些字符 ⇒ print 直接抛
# UnicodeEncodeError ⇒ **脚本在半路崩掉**，看起来像「跑到一半就死」（2026-11-03 实测）。
# 这里在开跑前把 stdout/stderr 兜住：显式设了 PYTHONIOENCODING 就尊重它，否则强制
# UTF-8；无论如何错误处理都改成 replace ⇒ **永不因编码崩**。
# ⚠️ 本函数**内联**在本文件里（不抽公共模块）：交付包会把 build.py 自副本带走，
#    另起模块会让交付包里的 build.py 导入失败 ⇒ 客户手上直接 ImportError。
def _fix_console_encoding():
    for stream in (sys.stdout, sys.stderr):
        try:
            enc = None if os.environ.get("PYTHONIOENCODING") else "utf-8"
            stream.reconfigure(encoding=enc, errors="replace")
        except Exception:
            pass


_fix_console_encoding()

HERE = os.path.dirname(os.path.abspath(__file__))
TEMPLATE_INDEX = os.path.join(HERE, "template", "index.html")
TEMPLATE_TRIPLES = os.path.join(HERE, "template", "triples.html")
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

    # ---- 附加：同一对节点不得挂多种关系类型 ----
    # （画布上会连出两条平行边；语义上等于对同一对节点说了两句话）
    pair_types = {}
    for e in edges:
        key = (e.get("source"), e.get("target"))
        pair_types.setdefault(key, set()).add(str(e.get("type")))
    multi = sorted("%s->%s:%s" % (k[0], k[1], "/".join(sorted(v)))
                   for k, v in pair_types.items() if len(v) > 1)
    rep.add("附L", "同一对节点只挂一种关系（%s）" % tag, not multi,
            ("多种关系 %d 对：%s" % (len(multi), "; ".join(multi[:8]))) if multi
            else "%d 对节点各有唯一关系" % len(pair_types))

    # ---- 附加：每条 evidence 都得有对应的文献节点，且连上 SUPPORTED_BY 边 ----
    # （⛔ 不拿 evidence.ref 当连接键 —— 两题里它不是 join key，会大面积误报；
    #   按**标题** join + 查 SUPPORTED_BY 边，才是数据里真正的连接方式。）
    # 真踩过：文献节点在收窄时被删、但引用它的 evidence 还留在节点上 ⇒
    #   页面上「文献出处」点得到标题，图里却查不到那条出处。
    ref_by_title = {}
    for n in nodes:
        if n.get("type") != "Reference":
            continue
        ref_by_title.setdefault(str(n.get("name") or ""), n.get("id"))
        for ev in (n.get("evidence") or []):
            if ev.get("title"):
                ref_by_title.setdefault(str(ev["title"]), n.get("id"))
    supported_pairs = set((e.get("source"), e.get("target")) for e in edges
                           if e.get("type") == "SUPPORTED_BY")
    ev_orphan, ev_noedge = [], []
    for n in nodes:
        if n.get("type") == "Reference":
            continue
        for ev in (n.get("evidence") or []):
            title = str(ev.get("title") or "")
            if not title:
                continue
            rid = ref_by_title.get(title)
            if rid is None:
                ev_orphan.append("%s→《%s》无对应文献节点" % (n.get("name"), title[:28]))
            elif (n.get("id"), rid) not in supported_pairs:
                ev_noedge.append("%s→《%s》没有 SUPPORTED_BY 边" % (n.get("name"), title[:28]))
    rep.add("附O", "每条出处都有文献节点且连上边（%s）" % tag,
            not ev_orphan and not ev_noedge,
            ("；".join((ev_orphan + ev_noedge)[:8]))
            if (ev_orphan or ev_noedge) else "全部出处都能在图里点到")

    # ---- 附加：摘要里点名的节点必须够得着 ----
    # 「护理预防」的摘要列了 5 条措施、点进去一条都没有 —— 这类「摘要承诺 vs 图里没有」
    # 是客户自检脚本查不出来的，只能自己盯。规则：摘要里出现的其他节点名
    # （≥3 字、且不是在另一个在场节点名里被顺带包含的），必须 2 跳内够得到。
    adj = {}
    for e in edges:
        # ⛔ 文献边不算「够得着」的路径 —— 共享同一篇出处的节点之间都隔着文献节点，
        #    走文献边会让任何两个节点都变成 2 跳可达，判据就废了。
        #    口径与前端画布一致：文献边默认隐藏，不承载知识关系。
        rel = rel_by_key.get(str(e.get("type") or ""))
        label = str((rel or {}).get("label") or e.get("label") or "")
        if "文献" in label:
            continue
        adj.setdefault(e.get("source"), set()).add(e.get("target"))
        adj.setdefault(e.get("target"), set()).add(e.get("source"))

    def reachable2(start):
        seen, frontier = set([start]), set([start])
        for _ in range(2):
            nxt = set()
            for x in frontier:
                nxt |= adj.get(x, set())
            nxt -= seen
            seen |= nxt
            frontier = nxt
        return seen

    node_names = [(n.get("id"), str(n.get("name") or "")) for n in nodes]
    # ⚠️ **文献节点不参与附P 判定**（2026-11-05 修正）
    #    附P 管的是「摘要承诺了一个图里够不着的**内容**节点」—— 那是缺陷。
    #    但摘要里写「出处：某某指南」是**正常写法**，文献节点是**出处**不是内容；
    #    而且文献边本来就被排除在可达路径外（否则任何两节点都 2 跳可达，判据失效）
    #    ⇒ 拿文献名去卡附P = 逼着作者不敢写出处。
    content_names = [(n.get("id"), str(n.get("name") or ""))
                     for n in nodes if n.get("type") != "Reference"]
    # 文献节点名 —— 摘要里出现文献名时，它内部的**内容节点名子串**不算「点名」
    # （例：文献名「影像科碘对比剂输注安全专家共识」里含「碘对比剂」；
    #     若不排除，会把「写了出处」误判成「承诺了一个够不着的节点」）
    ref_names = [str(n.get("name") or "") for n in nodes if n.get("type") == "Reference"]
    unreach = []
    for n in nodes:
        if n.get("type") == "Reference":
            continue
        summ = str(n.get("summary") or "")
        if not summ:
            continue
        present = [nm for _i, nm in content_names if nm and len(nm) >= 3 and nm in summ]
        for nid, nm in content_names:
            if nid == n.get("id") or not nm or len(nm) < 3 or nm not in summ:
                continue
            # 若它是另一个**在场**节点名的子串（顺带包含），不算点名
            if any(nm != other and nm in other for other in present):
                continue
            # 若它只出现在某个**文献名内部**（是文献名的一部分），不算点名
            if any(nm != rn and nm in rn for rn in ref_names):
                continue
            if nid not in reachable2(n.get("id")):
                unreach.append("%s 的摘要提到「%s」但 2 跳内到不了" % (n.get("name"), nm))
    rep.add("附P", "摘要点名的节点够得着（%s）" % tag, not unreach,
            ("；".join(unreach[:8])) if unreach else "摘要点名的节点都能到达")

    # ---- 附加：每条「要点」都必须有可回溯的出处 ----
    # 节点内容少 ⇒ 客户说「每个节点只说了一个标题的感觉」⇒ 加 `details`（要点数组）。
    # ⛔ 要点不许是空话：每条都要指到**图里真实存在的文献节点**，且正文非空。
    # ⚠️ **客户临床实践的例外**（2026-11-05）：客户口述的临床做法（如「新磺片加五黄油外敷」
    #    联合方案）**查不到文献** —— 但它不能因此从图上消失，也不能冒充有文献。
    #    ⇒ 这类要点必须显式标 `src: "__CLIENT__"`，且正文里必须写明证据状态
    #      （待核 / 跨适应证外推）。判据 = **显式标记 + 正文含证据状态说明**，
    #      不是「有没有文献」—— 混进来的每条都必须是真文献。
    ref_ids = set(n.get("id") for n in nodes if n.get("type") == "Reference")
    det_bad = []
    det_total = 0
    det_client = 0
    for n in nodes:
        for d in (n.get("details") or []):
            det_total += 1
            if not isinstance(d, dict):
                det_bad.append("%s 的要点不是对象" % n.get("name")); continue
            if not str(d.get("v") or "").strip():
                det_bad.append("%s 的要点缺正文" % n.get("name")); continue
            if not str(d.get("k") or "").strip():
                det_bad.append("%s 的要点缺标题" % n.get("name")); continue
            src = d.get("src")
            if src == "__CLIENT__":
                # 客户临床实践：必须有出处标记 + 正文写明证据状态
                det_client += 1
                if not any(kw in str(d.get("v") or "") for kw in
                           ("待核", "无任何", "证据状态", "跨适应证", "未披露")):
                    det_bad.append(
                        "%s 的客户实践要点没有写明证据状态（待核 / 无文献 / 跨适应证外推）"
                        % n.get("name"))
                continue
            if not src:
                det_bad.append("%s 的要点没有出处（src）" % n.get("name")); continue
            if src not in ref_ids:
                det_bad.append("%s 的要点出处 %s 不是图里的文献节点" % (n.get("name"), src))
    rep.add("附Q", "每条要点都有可回溯的出处（%s）" % tag, not det_bad,
            ("；".join(det_bad[:8])) if det_bad
            else "%d 条要点全部指到图内文献节点（其中 %d 条为客户临床实践，已标证据状态）"
                 % (det_total, det_client))

    # ---- 附加：患者层的「检查后须知」每条都要挂在有出处的节点上 ----
    # （与 P3 / P4 同一道闸：患者层是站内唯一直接对患者说话的内容）
    pdata = None
    try:
        ppath = find_patient_source(path, topic_key)
        if ppath:
            with open(ppath, "r", encoding="utf-8") as pf:
                pdata = json.load(pf)
    except Exception:
        pdata = None
    if pdata:
        ac_bad = []
        ac = pdata.get("aftercare") or []
        for a in ac:
            nid = a.get("nodeId")
            if nid not in idset:
                ac_bad.append("须知条目引用了图里没有的节点 %s" % nid)
                continue
            tgt = by_id0 = None
            for x in nodes:
                if x.get("id") == nid:
                    tgt = x; break
            if tgt is not None and not (tgt.get("evidence") or []):
                ac_bad.append("须知条目 %s 挂着的节点没有文献出处" % (a.get("plain") or nid))
        rep.add("附R", "患者层「检查后须知」每条都挂在有出处的节点上（%s）" % tag, not ac_bad,
                ("；".join(ac_bad[:6])) if ac_bad else "%d 条须知全部有出处" % len(ac))

    # ---- 附加：节点宣称的「覆盖范围」必须在图里真有着落 ----
    # （收窄过内容时，属性文字常忘了改 —— 页面上仍宣称覆盖已删掉的那一块，
    #   客户看到的就是「内容不对」。真踩过：覆盖范围写着「肾功能保护」，
    #   而肾功能那一支在收窄时已删、客户明说不要。）
    # ⛔ 判据不写死任何题目标识：只看属性键里带「覆盖」的项。
    all_names = set()
    for n in nodes:
        all_names.add(str(n.get("name") or ""))
        for al in (n.get("aliases") or []):
            all_names.add(str(al))
    scope_bad = []
    for n in nodes:
        for a in (n.get("attrs") or []):
            if not isinstance(a, dict):
                continue
            if "覆盖" not in str(a.get("k") or ""):
                continue
            for part in re.split(r"[·、，,;；/]+", str(a.get("v") or "")):
                part = part.strip()
                if not part:
                    continue
                if not any(part in x or x in part for x in all_names):
                    scope_bad.append("%s[%s] 宣称「%s」但图里没有" % (
                        n.get("name"), a.get("k"), part))
    rep.add("附N", "宣称的覆盖范围在图里有着落（%s）" % tag, not scope_bad,
            ("；".join(scope_bad[:8])) if scope_bad else "覆盖范围声明与图内节点一致")

    # ---- 附加：有主张的节点不得用空话代替内容 ----
    # 「本图谱中……的总称」这类同义反复 = 读者读完等于没读。
    # ⛔ 判据不写死任何节点名 / 类型名以外的题目标识；
    #    Reference 节点豁免（书目性摘要本就是元描述）。
    META_TALK = ("本图谱", "本文", "本模块", "本单元", "本页面")
    empty_sum, meta_sum = [], []
    for n in nodes:
        if n.get("type") == "Reference":
            continue
        s = str(n.get("summary") or "").strip()
        if not s:
            empty_sum.append("%s(%s)" % (n.get("name"), n.get("type")))
        elif any(m in s for m in META_TALK):
            meta_sum.append("%s(%s)" % (n.get("name"), n.get("type")))
    detail_m = []
    if empty_sum:
        detail_m.append("空摘要 %d：%s" % (len(empty_sum), "; ".join(empty_sum[:8])))
    if meta_sum:
        detail_m.append("元话术摘要 %d：%s" % (len(meta_sum), "; ".join(meta_sum[:8])))
    rep.add("附M", "节点摘要有实质内容（%s）" % tag,
            not empty_sum and not meta_sum,
            "；".join(detail_m) if detail_m else "非文献节点摘要全部有内容")

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
| 看三元组表 | 双击 `triples.html` —— 每条关联关系一行（主体 · 关系 · 客体），可搜索、可下 CSV |
| 上线 | 整个目录原样丢进任意静态托管（对象存储 / CDN / 静态站点），无需服务端配置 |

⛔ 页面**不请求任何后端接口**，也**不连数据库**——数据随目录发布，检索在浏览器里算。

## 二、目录结构

```
{topic_key}-kg/
├── index.html                     单页图谱（卡片流 + 全景图 + 检索 + 节点详情）
├── triples.html                   三元组表页（每条关联关系一行 · 可搜索 · 可下 CSV）
├── lib/echarts.min.js             图形库（本地内置 · 断网也能打开）
├── data/{topic_key}-graph.json     图谱数据（自包含：类型定义 + 节点 + 边 + 文献出处）
├── data/{topic_key}-graph.js       同一份数据的 JS 副本（页面直接读它）
├── data/{topic_key}-triples.csv    5 列表原件（输入形态 · 可直接重新生成图谱数据）
├── data/{topic_key}-triples.js     5 列表的 JS 副本（三元组页直接读它）
├── data/{topic_key}-patient.json   患者层数据（可选：一句导语 + 免责声明 + 就医警示）
├── data/{topic_key}-patient.js     同一份数据的 JS 副本（页面直接读它）
├── data/search-terms.json         检索词清单（校验规则第 5 条的对照夹具）
├── build.py                       构建脚本（校验 + 重新生成）
├── README.md                      本文件
└── neo4j/                         可选 · Neo4j 导入包（非运行依赖）
    ├── nodes.csv
    ├── edges.csv
    └── import.cypher
```

## 三、页面两种形态（默认按屏幕宽度选）

| 形态 | 什么时候是它 | 里面有什么 |
|---|---|---|
| **知识浏览**（卡片流）| **手机默认** · 桌面也可用 | 一句导语 + 免责声明 → **分诊**（逐条点选「你现在有这些情况吗」→ 行动汇总 / 先观察）→ 分类卡流 → 词条卡 → 节点详情 |
| **全景图**（力导向画布）| 桌面默认 · 手机点右上角切过去 | 逐步展开的力导向图 + **只看这一圈**邻域 + 图例 + 检索高亮 |

**手机阅读模型（2026-11-04）**：

- **分诊优先**：就医警示不是静态清单 —— 逐条点选后直接给出「马上告诉医护人员」或「先观察」的结论。
- **详情卡 = 路径卡**：面包屑记来路；关联节点按关系分组（→ 从本节点指出 / ← 指向本节点）；文献出处默认折叠在最后。
- **只看这一圈**：选中节点后点「在关系图里看这一圈」，画布只画当前节点 + 一跳邻居（手机 10 个 / 宽屏 16 个，其余在角标里计数），点邻居可以继续换中心走。
- **文献边默认隐藏**：文献边约占全部边的一半，画出来会盖住知识结构；图例里可一键打开。

⛔ **为什么不把桌面画布缩小放到手机上**：节点一多，屏宽摊不开、字放不下 ——
那是结构问题，不是样式问题（缩小解决不了）。手机默认走卡片流；要看关系时用「只看这一圈」，
而不是把 92 个点缩成一屏。
⛔ **就医警示的每一条都挂在图谱里带文献出处的节点上** —— 构建时会逐条校验
（挂错节点 / 节点没出处 ⇒ 构建直接中止）。

## 四、怎么用 build.py

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

## 五、检索怎么用

| 输入 | 命中通道 |
|---|---|
| 节点名称 / 别名 / 简介 / 属性 | 节点文本通道（大小写不敏感 · 首尾空格忽略 · 双向子串）|
| 文献类型（指南 / 共识 / 系统评价 / Meta 分析 …）| 文献类型通道 —— 命中**引用了该类型文献**的节点 |

英文文献类型词（`guidelines` / `systematic reviews` / `meta analysis`）与中文类型词命中**同一批节点**。
⛔ 节点级同义词（英文写法 / 旧称 / 错字写法）一律写在数据文件的 `aliases` 里，不写死在代码里。

## 六、数据说明

- 数据文件自包含：`meta`（题目元数据）· `nodeTypes`（类型定义，**样式随数据走**）·
  `relationTypes`（关系定义）· `nodes` · `edges`。
- 节点类型未在 `nodeTypes` 里声明时，页面走兜底样式，不会白屏。
- 文献出处挂在节点的 `evidence` 上，页面详情面板里逐条显示作者 / 标题 / 期刊 / 年份。
- ⛔ **没有真实出处的节点不要写进图谱** —— 校验脚本会按缺失项报出来。

## 七、Neo4j 导入包（可选）

`neo4j/` 里是给**想自己入库**的人准备的：把两个 csv 放进 Neo4j 的 import 目录，
在 Browser 里执行 `import.cypher`。它是**可选件**，页面本身不需要数据库。

---
生成于 {generated_at}
"""


# 症状类节点的类型组 —— **口径只在数据侧定义一次**（前端不许写死类型 key · 判据 #4）
SYMPTOM_TYPE_KEYS = ("SymptomSign", "SymptomCategory")

# 文献类型 → 证据层级（客户 2026-11-11 问「指南、文献、书籍都是多少」）
# ⛔ 这张表住在**构建侧**（不在前端）—— 前端只读现算好的结果，
#    换一道题换了类型词，页面自己跟着变，不用改代码。
LIT_LEVELS = (
    ("指导性文件（指南 / 共识 / 规范 / 标准 / 建议 / 推荐 / 立场声明 / 最佳证据）",
     ("指南", "规范", "标准", "共识", "建议", "推荐", "推荐实践",
      "推荐实践（证据总结）", "立场声明", "声明", "最佳证据")),
    ("证据汇总（系统评价 / Meta 分析）",
     ("系统评价", "Meta分析", "Meta 分析", "Meta 分析（网状）")),
    ("综述", ("综述",)),
    ("原始研究（对照研究 / 队列 / 病例 / 调查 / 临床审计）",
     ("对照研究", "队列研究", "病例系列", "病例报告", "调查", "临床审计")),
    ("书籍 / 药品说明书", ("书籍", "药品说明书")),
)


def compute_literature_stats(data):
    """文献构成统计 —— **从图谱数据现算**：按证据类型 + 按证据层级

    客户 2026-11-11 问「97 篇都是什么文献，指南、文献、书籍都是多少」——
    ⇒ 页面上要能直接看到，不用他再问一轮。

    口径：每篇文献节点取它的**文献类型**（evidence[].type，或 attrs 里的
    「文献类型 / 类型 / evidenceType」）—— 一篇只取第一个（实测 97 篇都是单一类型）。
    """
    from collections import Counter
    by_type = Counter()
    refs = 0
    for n in (data.get("nodes") or []):
        if n.get("type") != "Reference":
            continue
        refs += 1
        t = ""
        for ev in (n.get("evidence") or []):
            if isinstance(ev, dict) and str(ev.get("type") or "").strip():
                t = str(ev["type"]).strip()
                break
        if not t:
            for a in (n.get("attrs") or []):
                if isinstance(a, dict) and a.get("k") in ("文献类型", "类型", "evidenceType"):
                    t = str(a.get("v") or "").strip()
                    if t:
                        break
        if t:
            by_type[t] += 1
    by_level = []
    used = set()
    for label, keys in LIT_LEVELS:
        n = sum([by_type.get(k, 0) for k in keys])
        used.update(keys)
        if n:
            by_level.append({"label": label, "count": n})
    other = sum([v for k, v in by_type.items() if k not in used])
    if other:
        by_level.append({"label": "其他类型", "count": other})
    return {
        "total": refs,
        "byType": [{"type": k, "count": v} for k, v in by_type.most_common()],
        "byLevel": by_level,
    }


def write_literature_js(stats, dst_path):
    """文献构成 —— 单独一个 JS 副本（页面直接读它；数据随页内联，不走 fetch）"""
    with open(dst_path, "w", encoding="utf-8", newline="\n") as f:
        f.write("window.KG_LIT = %s;\n"
                % json.dumps(stats, ensure_ascii=False, separators=(",", ":")))
    return True


def compute_scale_stats(data):
    """规模数字 —— **从图谱数据现算**，返回给页面直接显示

    ⛔ 为什么要有这一层（2026-11-11 客户当场抓到的口径不一致）：
       页面上写「266 个实体」，而聊天里报的是「内容实体 157 + 症状实体 43」——
       后两个是**互相包含**的数，客户按「只要总数」把两个一加 = 200 ⇒ 与 266 对不上，
       客户以为数据有问题。**根因是同一件事给了两个口径、且没说是包含关系。**
       ⇒ 这里把口径**固定成互不重叠、可相加**的一组：
           节点总数 = 知识实体 + 文献节点
           知识实体 = 节点总数 − 文献节点（**含框架节点** —— 框架节点也是真节点）
           症状类节点 = 知识实体里类型属于症状组的那些（**是子集，单列**）
       页面与对外口径都用这一组 ⇒ 客户再遇到数，只会自己加出 266。
    """
    nodes = data.get("nodes") or []
    refs = [n for n in nodes if n.get("type") == "Reference"]
    knowledge = [n for n in nodes if n.get("type") != "Reference"]
    symptoms = [n for n in knowledge if n.get("type") in SYMPTOM_TYPE_KEYS]
    rels = set()
    for e in (data.get("edges") or []):
        rels.add(str(e.get("label") or e.get("type") or ""))
    return {
        "nodes": len(nodes),
        "references": len(refs),
        "knowledge": len(knowledge),
        "symptoms": len(symptoms),
        "relations": len([r for r in rels if r]),
        "edges": len(data.get("edges") or []),
    }


def copy_if_different(src, dst):
    """拷贝 —— 源与目标是同一个文件时跳过（就地重建会撞上）"""
    if not os.path.exists(src):
        return False
    if os.path.abspath(src) == os.path.abspath(dst):
        return False
    shutil.copyfile(src, dst)
    return True


def read_triples_csv(csv_path):
    """读 5 列表 → 行数组（每行 5 列，已去 BOM · 去空行）

    ⛔ 表头行（sub_type / 类型 / src_type）不算数据行 —— 页面上的表头是另一套中文。
    """
    with open(csv_path, "r", encoding="utf-8-sig", newline="") as f:
        rows = [r for r in csv.reader(f) if r and any(str(c).strip() for c in r)]
    if rows and rows[0] and str(rows[0][0]).strip() in ("sub_type", "类型", "src_type"):
        rows = rows[1:]
    out = []
    for r in rows:
        cells = [str(c).strip() for c in r[:5]]
        if len(cells) < 5:
            continue
        out.append(cells)
    return out


def write_triples_js(csv_path, dst_path, type_labels=None, stats=None):
    """把 5 列表写成 JS 副本 —— 三元组页（triples.html）直接读它

    为什么要有 JS 副本：页面是 `file://` 双击直开的静态页，`fetch` CSV 会被浏览器的
    跨域规则挡住（和图谱数据同一道坎）⇒ 数据随页面内联，不走 fetch。

    type_labels —— 节点类型 key → 中文标签（来自数据文件的 nodeTypes）。
    ⛔ CSV 里的类型列是**英文 key**（客户规范 §三 的输入形态）⇒ 页面上换成中文
       标签才读得懂；英文 key 保留在单元格的 title 里（要核对原始形态时可看）。

    stats —— 规模数字（节点 / 知识实体 / 文献 / 症状类）。**由构建时从图谱数据现算**，
    ⛔ 不写死在页面上 —— 也不在前端写死类型 key（判据 #4）⇒ 口径只在数据侧定义一次。
    """
    rows = read_triples_csv(csv_path)
    payload = {"rows": rows, "labels": type_labels or {}, "stats": stats or {}}
    with open(dst_path, "w", encoding="utf-8", newline="\n") as f:
        f.write("window.KG_TRIPLES = %s;\n"
                % json.dumps(payload, ensure_ascii=False, separators=(",", ":")))
    return len(rows)


# --------------------------------------------------------------------------
# 患者层（给患者看的那一层：一句导语 + 免责声明 + 就医警示）
# --------------------------------------------------------------------------
# ⛔ 为什么单独一个文件，不塞进图谱 JSON：
#    图谱 JSON 是**给专业读者**的（节点 / 边 / 文献出处），客户部的验收判据与
#    数据自检脚本都对着它 ⇒ 动它会牵动一整套校验；患者层是**给患者看的**
#    （通俗表达 + 什么时候该找医生）—— 两者受众不同、判据也不同。
# ⭐ 核心判据 P4：就医警示的每一条都必须挂在**图谱里已存在、且带文献出处**的节点上
#    —— 这一条从机制上保证「患者层不会出现没有出处的医学断言」。

PATIENT_REQUIRED_FIELDS = ("intro", "disclaimer")


def check_patient_data(pdata, data, topic_key):
    """校验患者层数据 —— 返回问题清单（空 = 通过）"""
    problems = []
    if not isinstance(pdata, dict):
        return ["P0 患者层文件不是一个 JSON 对象"]
    tk = pdata.get("topicKey")
    if tk != topic_key:
        problems.append("P1 topicKey 不一致：文件写的是 %r，本题是 %r" % (tk, topic_key))
    for f in PATIENT_REQUIRED_FIELDS:
        if not str(pdata.get(f) or "").strip():
            problems.append("P2 必填字段 %s 为空" % f)
    urgent = pdata.get("urgent")
    if urgent is None:
        urgent = []
    if not isinstance(urgent, list):
        problems.append("P3 urgent 不是一个数组")
        urgent = []
    nodes = {}
    for n in (data.get("nodes") or []):
        nodes[n.get("id")] = n
    for i, u in enumerate(urgent, 1):
        if not isinstance(u, dict):
            problems.append("P3 urgent 第 %d 条不是一个对象" % i)
            continue
        nid = u.get("nodeId")
        if not str(nid or "").strip():
            problems.append("P5 urgent 第 %d 条缺 nodeId" % i)
            continue
        if nid not in nodes:
            problems.append("P3 urgent 第 %d 条的 nodeId %r 不在图谱里 —— "
                            "患者层不能引用图谱里没有的节点" % (i, nid))
            continue
        if not str(u.get("plain") or "").strip():
            problems.append("P5 urgent 第 %d 条（%s）缺 plain" % (i, nid))
        if not str(u.get("action") or "").strip():
            problems.append("P5 urgent 第 %d 条（%s）缺 action" % (i, nid))
        if not (nodes[nid].get("evidence") or []):
            problems.append("P4 urgent 第 %d 条（%s）对应的节点没有文献出处 —— "
                            "没有出处的医学断言不许出现在患者层" % (i, nid))
    return problems


def find_patient_source(src_path, topic_key):
    """患者层数据文件的位置 —— **图谱 JSON 旁边**的 <topicKey>-patient.json

    放在旁边而不是另设参数：交付包里 data/<key>-graph.json 与 data/<key>-patient.json
    并排 ⇒ 客户拿到包自己重跑 build.py 时，患者层也会被一起带上（不用记额外参数）。
    """
    cand = os.path.join(os.path.dirname(os.path.abspath(src_path)),
                        "%s-patient.json" % topic_key)
    return cand if os.path.exists(cand) else None


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
    csv_dst = os.path.join(data_dir, "%s-triples.csv" % topic_key)
    copy_if_different(csv_src, csv_dst)

    # 3b-2 · 5 列表的 JS 副本 —— 三元组页（triples.html）直接读它
    #        （页面走 file:// 直开 ⇒ fetch CSV 会被跨域挡住 ⇒ 数据内联成 JS）
    triples_rows = 0
    if os.path.exists(csv_dst):
        try:
            type_labels = dict([(str(t.get("key")), str(t.get("label") or t.get("key")))
                                for t in (data.get("nodeTypes") or [])
                                if isinstance(t, dict)])
            triples_rows = write_triples_js(
                csv_dst, os.path.join(data_dir, "%s-triples.js" % topic_key),
                type_labels=type_labels,
                stats=compute_scale_stats(data))
        except Exception as e:
            raise StructureGateError("5 列表转 JS 失败：%s（%s）" % (csv_dst, e))

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

    # 3b-4 · 文献构成统计（客户 2026-11-11 问「指南、文献、书籍都是多少」）
    #        ⇒ 页面上的「文献支撑」总账要能直接看到类型与层级，别让他再问一轮。
    lit_stats = compute_literature_stats(data)
    try:
        write_literature_js(lit_stats,
                             os.path.join(data_dir, "%s-literature.js" % topic_key))
        rep.add("附U", "文献构成统计已产出", True,
                "%d 篇 · %d 类类型 · %d 个层级"
                % (lit_stats["total"], len(lit_stats["byType"]),
                   len(lit_stats["byLevel"])))
    except Exception as e:
        raise StructureGateError("文献构成统计产出失败：%s" % e)

    # 3d · 患者层（可选件：图谱 JSON 旁边的 <topicKey>-patient.json）
    #       —— 有就校验 + 随包带上；没有就这一层不出现（页面自动退回通用免责口径）
    patient_src = find_patient_source(src_path, topic_key)
    patient_script = ""
    if patient_src:
        try:
            with open(patient_src, "r", encoding="utf-8") as f:
                pdata = json.load(f)
        except Exception as e:
            raise StructureGateError("患者层文件解析失败：%s（%s）" % (patient_src, e))
        pproblems = check_patient_data(pdata, data, topic_key)
        if pproblems:
            raise StructureGateError(
                "患者层校验不通过 —— **已中止构建**\n"
                "文件：%s\n%s"
                % (patient_src, "\n".join("   · " + x for x in pproblems)))
        copy_if_different(patient_src, os.path.join(data_dir, "%s-patient.json" % topic_key))
        with open(os.path.join(data_dir, "%s-patient.js" % topic_key),
                  "w", encoding="utf-8", newline="\n") as f:
            f.write("window.KG_PATIENT = %s;\n"
                    % json.dumps(pdata, ensure_ascii=False, indent=2))
        patient_script = '<script src="./data/%s-patient.js"></script>' % topic_key
        rep.add("附P", "患者层校验（就医警示挂在有出处的节点上）", True,
                "文件：%s · 警示 %d 条" % (os.path.basename(patient_src),
                                          len(pdata.get("urgent") or [])))
    else:
        rep.add("附P", "患者层校验（就医警示挂在有出处的节点上）", True,
                "本题目没有 <topicKey>-patient.json —— 患者层不出现（页面用通用免责口径）")

    # 4 · 图形库
    copy_if_different(ECHARTS_SRC, os.path.join(lib_dir, "echarts.min.js"))

    # 5 · 页面（模板在脚本旁边时重建；交付目录里没有模板就保留现有页面）
    index_dst = os.path.join(out_dir, "index.html")
    if os.path.exists(TEMPLATE_INDEX):
        with open(TEMPLATE_INDEX, "r", encoding="utf-8") as f:
            tpl = f.read()
        page_html = (tpl
                     .replace("{{TOPIC_KEY}}", topic_key)
                     .replace("{{PATIENT_SCRIPT}}", patient_script))
        # 5a · 占位符必须全部替换掉 —— 漏一个 {{XXX}} 就会以字面量出现在页面上
        leftover = re.findall(r"\{\{[A-Z_]+\}\}", page_html)
        if leftover:
            raise StructureGateError(
                "页面模板有未替换的占位符：%s —— **已中止，未写出 index.html**"
                % " · ".join(sorted(set(leftover))))
        # 5b · **写盘前**先过静态结构闸门 —— 坏页面不许落盘
        #      （本次线上缺陷就是「坏页面进了交付目录」才被客户扫码发现）
        static_problems = check_html_static(page_html)
        if static_problems:
            raise StructureGateError(
                "页面静态结构不通过 —— **已中止，未写出 index.html**\n"
                "文件：%s\n%s"
                % (index_dst, "\n".join("   · " + x for x in static_problems)))
        with open(index_dst, "w", encoding="utf-8", newline="\n") as f:
            f.write(page_html)
    elif not os.path.exists(index_dst):
        raise RuntimeError("找不到页面模板，且目录里没有现成的 index.html：%s" % out_dir)

    # 5-2 · 三元组表页（客户要「直接看到那张表」时打开的就是它）
    #        ⛔ 页面里的数据来自 data/<key>-triples.js（上面 3b-2 生成的），
    #           页面本身**不 fetch** —— file:// 双击直开也能用。
    triples_dst = os.path.join(out_dir, "triples.html")
    if os.path.exists(TEMPLATE_TRIPLES):
        with open(TEMPLATE_TRIPLES, "r", encoding="utf-8") as f:
            tpl_t = f.read()
        page_t = tpl_t.replace("{{TOPIC_KEY}}", topic_key)
        leftover_t = re.findall(r"\{\{[A-Z_]+\}\}", page_t)
        if leftover_t:
            raise StructureGateError(
                "三元组页模板有未替换的占位符：%s —— **已中止，未写出 triples.html**"
                % " · ".join(sorted(set(leftover_t))))
        static_t = check_html_static(page_t, anchors=())
        if static_t:
            raise StructureGateError(
                "三元组页静态结构不通过 —— **已中止，未写出 triples.html**\n"
                "文件：%s\n%s"
                % (triples_dst, "\n".join("   · " + x for x in static_t)))
        with open(triples_dst, "w", encoding="utf-8", newline="\n") as f:
            f.write(page_t)

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
    return out_dir, triples_rows


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


# --------------------------------------------------------------------------
# 6 · 结构闸门 —— 标签配平 + JS 语法 + 首屏渲染
#
# 起因（2026-11-03 线上缺陷）：图谱页「一直转圈圈（正在加载图谱数据…）」——
# 根因是模板里 KG-CORE 内联 <script> 块**缺一个 </script>** ⇒ 浏览器 raw-text
# 解析把后面那个 <script> 当成 JS 源码 ⇒ 解析期抛 Unexpected token '<' ⇒
# window.KGCORE 未定义 ⇒ 渲染 IIFE 整块没执行 ⇒ #loading 遮罩永不隐藏。
#
# 为什么旧的四道自检全绿：它们按 KG-CORE-START/END 标记把代码块抽出来在 Node 里
# 跑，测的是**逻辑**；没有任何一道在问「标签配平吗」「这页真渲染出来了吗」。
# 本闸门补的就是这两问 —— 把这类缺陷拦在构建期，而不是等客户扫码才发现。
#
# 三层（**任何一层「跳过」都会打印原因 —— 不静默省略**）：
#   S · 静态结构（纯标准库 · 永远跑）
#   J · JS 语法（node --check · 没 node 则显式跳过）
#   R · 首屏渲染（playwright · 没装 / 起不来则显式跳过）
#
# ⛔ 闸门代码内联在 build.py 里（不另起模块）：交付包会把 build.py 自副本带走，
#    另起模块会让交付包里的 build.py 导入失败 ⇒ 结构闸门在客户手上就失效了。
# --------------------------------------------------------------------------

STRUCT_GATE_VERSION = "2026-11-03-3"

# 页面上必须存在的锚点 —— 缺一个 = 渲染逻辑走不到那一步
REQUIRED_ANCHORS = (
    ('id="loading"', "首屏遮罩 #loading"),
    ('id="chart"', "图谱容器 #chart"),
    ('id="viewList"', "列表视图容器 #viewList"),
    ('id="viewGraph"', "画布视图容器 #viewGraph"),
    ("KGCORE", "window.KGCORE 赋值"),
    ("KG_GRAPH", "图谱数据 window.KG_GRAPH 引用"),
)

# 画布上「非透明像素」低于此数 = 什么都没画出来（空白页）
MIN_PAINTED_PIXELS = 1000

# 渲染检查的等待上限（毫秒）
RENDER_TIMEOUT_MS = 15000

# 移动端检查用的视口（主流竖屏机型 —— 卡片流是手机上的默认形态）
MOBILE_VIEWPORT = {"width": 390, "height": 844}


class StructureGateError(Exception):
    """结构闸门不通过 —— 构建中止（**不产出坏产物**）"""


def split_raw_text_bodies(html):
    """把每个 <script> / <style> 的正文切出来（标准库 html.parser）。

    HTMLParser 在 script / style 内走 CDATA 模式 —— 正文直到对应的闭标签才结束，
    这正是浏览器的 raw-text 行为 ⇒ 用它能看出「正文里混进了裸标签字面量」。

    ⚠️ 这是本次缺陷能被抓到的关键：浏览器把开标签当 JS 源码解析时，
       出错的是**正文内容**，而不是标签计数 —— 只比计数会误判成「配平」。
    """
    class _Splitter(HTMLParser):
        def __init__(self):
            HTMLParser.__init__(self, convert_charrefs=False)
            self.items = []          # [{tag, attrs, body}]
            self._cur = None

        def handle_starttag(self, tag, attrs):
            if tag in ("script", "style"):
                self._cur = {"tag": tag, "attrs": dict(attrs), "body": []}

        def handle_startendtag(self, tag, attrs):
            pass                     # HTML 没有自闭合的 <script/> —— 忽略

        def handle_endtag(self, tag):
            if self._cur is not None and tag == self._cur["tag"]:
                self._cur["body"] = "".join(self._cur["body"])
                self.items.append(self._cur)
                self._cur = None

        def handle_data(self, data):
            if self._cur is not None:
                self._cur["body"].append(data)

        def handle_entityref(self, name):
            if self._cur is not None:
                self._cur["body"].append("&%s;" % name)

        def handle_charref(self, name):
            if self._cur is not None:
                self._cur["body"].append("&#%s;" % name)

    p = _Splitter()
    p.feed(html)
    p.close()
    return p.items


def check_html_static(html, anchors=None):
    """静态结构检查（纯标准库）—— 返回问题清单（空 = 通过）。

    每条问题都带编号（S1/S2/…），便于回报时指名道姓地说清「哪一项不匹配」。

    anchors —— 必备锚点（needle, 说明）序列；默认用图谱页那套。
               传空元组 = 只查标签配平与裸标签字面量（副页面用）。
    """
    if anchors is None:
        anchors = REQUIRED_ANCHORS
    problems = []
    low = html.lower()
    # 计数前先剥掉 HTML 注释 —— 注释里写「<script>」是说明文字，不是标签
    stripped = re.sub(r"<!--.*?-->", "", html, flags=re.S)
    slow = stripped.lower()

    # S1 · script 标签配平
    n_open = slow.count("<script")
    n_close = slow.count("</script>")
    if n_open != n_close:
        problems.append(
            "S1 script 标签不配平：开标签 <script × %d，闭标签 </script> × %d（差 %+d）"
            " —— 浏览器会从开标签一路 raw-text 读到下一个闭标签，"
            "中间的标记被当源码解析" % (n_open, n_close, n_open - n_close))

    # S2 · style 标签配平
    so = slow.count("<style")
    sc = slow.count("</style>")
    if so != sc:
        problems.append("S2 style 标签不配平：<style × %d，</style> × %d" % (so, sc))

    # S3 · 正文里混入裸标签字面量（**本次线上缺陷的直接指纹**）
    seq = {"script": 0, "style": 0}
    for item in split_raw_text_bodies(html):
        tag = item["tag"]
        seq[tag] = seq.get(tag, 0) + 1
        body_low = item["body"].lower()
        for probe in ("script", "style"):
            if ("<" + probe) in body_low:
                problems.append(
                    "S3 第 %d 个 <%s> 元素的正文里出现了裸露的 <%s 字面量 —— "
                    "浏览器会把后续内容整段当 %s 源码解析，解析期抛错 -> 该脚本整块不执行"
                    % (seq[tag], tag, probe, probe))

    # S4 · 必备锚点
    for needle, human in anchors:
        if needle not in html:
            problems.append("S4 缺少必备结构：%s（找的是 %s）" % (human, needle))

    # S5 · KG-CORE 标记成对（检索层自测按这两个标记抽代码块）
    #     ⛔ 只对图谱页成立 —— 副页面（triples.html）没有检索核心，不查。
    if anchors is REQUIRED_ANCHORS:
        ns = html.count("KG-CORE-START")
        ne = html.count("KG-CORE-END")
        if ns != 1 or ne != 1:
            problems.append(
                "S5 KG-CORE 标记不成对：KG-CORE-START × %d / KG-CORE-END × %d"
                "（检索层自测按这两个标记抽代码块）" % (ns, ne))

    # S6 · 页面正文里不得有 NUL 字节
    #     真踩过：模板里一个本该是空格的字符写成了 NUL ⇒ 浏览器照样跑得通
    #     （NUL 是合法 JS 字符串字符）⇒ **没有任何运行时症状**，
    #     但 git 会因此把整个 HTML 判成二进制 ⇒ diff 全废、合并冲突看不懂、
    #     交付包里的文件带着不可见垃圾。静态结构层抓它最省事。
    if "\x00" in html:
        problems.append(
            "S6 页面里有 NUL 字节（%d 处）—— 浏览器可能照样跑，但 git 会把文件判成"
            "二进制（diff 全废），交付包里也带着不可见垃圾" % html.count("\x00"))

    return problems


def check_js_syntax(html):
    """内联 <script> 正文的 JS 语法检查（node --check）。

    返回 (问题清单, 跳过说明) —— 没 node 时跳过并**说明原因**（不静默）。
    这一层能在没有浏览器的情况下抓住「Unexpected token '<'」这一类解析期错误。
    """
    node = shutil.which("node")
    if not node:
        return [], "跳过（未找到 node 可执行文件 —— 本层要在无浏览器环境兜住 JS 解析期错误）"

    problems = []
    idx = 0
    for item in split_raw_text_bodies(html):
        if item["tag"] != "script":
            continue
        if item["attrs"].get("src"):
            continue                          # 外链脚本 —— 正文不在本文件里
        body = item["body"]
        if not body.strip():
            continue
        idx += 1
        # 临时文件放系统临时目录 —— 工具运行时产物，不落工作区
        with tempfile.TemporaryDirectory() as tmpdir:
            js_path = os.path.join(tmpdir, "inline-%d.js" % idx)
            with open(js_path, "w", encoding="utf-8", newline="\n") as f:
                f.write(body)
            proc = subprocess.run([node, "--check", js_path],
                                  capture_output=True, text=True,
                                  encoding="utf-8", errors="replace")
        if proc.returncode != 0:
            detail = (proc.stderr or proc.stdout or "").strip()
            first = " / ".join(detail.splitlines()[:3])
            problems.append("J1 第 %d 个内联 <script> 的 JS 语法不合法：%s" % (idx, first))
    return problems, ""


def check_render(index_path, timeout_ms=RENDER_TIMEOUT_MS):
    """首屏渲染检查 —— 真跑一次页面。

    返回 (问题清单, 跳过说明)：
      · playwright 没装 / 浏览器起不来 → 跳过并**说明原因**（不静默）
      · 页面本身有问题 → 问题清单（构建据此失败）

    断言：页面无未捕获异常 · #loading 遮罩已隐藏 · window.KGCORE 已定义 ·
          图谱数据非空 · canvas 已创建且画出了东西。
    """
    try:
        from playwright.sync_api import sync_playwright
    except Exception as e:
        return [], "跳过（本机没有 playwright：%s）" % e

    problems = []
    errors = []

    def _on_console(msg):
        if msg.type == "error":
            errors.append("console.error：%s" % msg.text)

    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch()
            try:
                page = browser.new_page(viewport={"width": 1440, "height": 900})
                page.on("pageerror", lambda e: errors.append("未捕获异常：%s" % e))
                page.on("console", _on_console)
                page.goto(_file_uri(index_path))
                try:
                    page.wait_for_function(
                        "() => { const e = document.getElementById('loading');"
                        " return !e || getComputedStyle(e).display === 'none'; }",
                        timeout=timeout_ms)
                    loading_hidden = True
                except Exception:
                    loading_hidden = False
                page.wait_for_timeout(1200)      # 等 ECharts 动画画完
                state = page.evaluate("""() => {
                    const cv = document.querySelector('#chart canvas');
                    let painted = -1;
                    if (cv) {
                        try {
                            const d = cv.getContext('2d')
                                .getImageData(0, 0, cv.width, cv.height).data;
                            painted = 0;
                            for (let i = 3; i < d.length; i += 4) {
                                if (d[i] !== 0) painted++;
                            }
                        } catch (e) { painted = -2; }
                    }
                    const l = document.getElementById('loading');
                    /* 画布是不是「逐步展开」的：首屏画出来的节点数应当少于总数 */
                    let rendered = -1;
                    try {
                        const inst = window.echarts &&
                            window.echarts.getInstanceByDom(document.getElementById('chart'));
                        rendered = inst
                            ? inst.getModel().getSeriesByIndex(0).getData().count() : -1;
                    } catch (e) { rendered = -2; }
                    return {
                        kgcore: typeof window.KGCORE,
                        kgcoreKeys: window.KGCORE ? Object.keys(window.KGCORE).length : -1,
                        nodes: window.KG_GRAPH ? (window.KG_GRAPH.nodes || []).length : -1,
                        edges: window.KG_GRAPH ? (window.KG_GRAPH.edges || []).length : -1,
                        rendered: rendered,
                        actions: ['pExpand', 'pLock', 'pRemove'].every(function (id) {
                            return !!document.getElementById(id);
                        }),
                        loading: l ? getComputedStyle(l).display : 'missing',
                        canvasW: cv ? cv.width : 0,
                        canvasH: cv ? cv.height : 0,
                        painted: painted
                    };
                }""")
            finally:
                browser.close()
    except Exception as e:
        return [], "跳过（playwright 起不来：%s）" % e

    # R1 · 页面级错误（解析期错误就在这里冒头）
    for msg in errors:
        problems.append("R1 页面报错：%s" % msg)

    # R2 · window.KGCORE 已定义
    if state["kgcore"] != "object":
        problems.append("R2 window.KGCORE 未定义（typeof = %s）—— 渲染逻辑整块没执行"
                        % state["kgcore"])
    elif state["kgcoreKeys"] < 1:
        problems.append("R2 window.KGCORE 是空对象 —— 检索核心没装载")

    # R3 · 数据非空
    if state["nodes"] <= 0:
        problems.append("R3 图谱数据为空（KG_GRAPH.nodes = %d）" % state["nodes"])

    # R4 · 首屏遮罩已隐藏
    if not loading_hidden or state["loading"] != "none":
        problems.append(
            "R4 首屏遮罩没隐藏（#loading 的 display = %s，等待 %d ms 后仍未隐藏）"
            " —— 客户看到的就是「一直转圈圈（正在加载图谱数据…）」"
            % (state["loading"], timeout_ms))

    # R5 · canvas 已创建
    if state["canvasW"] <= 0 or state["canvasH"] <= 0:
        problems.append("R5 #chart 里没有画布（canvas = %d × %d）"
                        % (state["canvasW"], state["canvasH"]))

    # R6 · 画布确实画出了东西
    if state["painted"] >= 0 and state["painted"] < MIN_PAINTED_PIXELS:
        problems.append("R6 画布上只有 %d 个非透明像素（阈值 %d）—— 图没画出来"
                        % (state["painted"], MIN_PAINTED_PIXELS))

    # R7 · 画布是「点选逐步延展」的：首屏只画一部分，不是一次铺满
    #      （一次铺满 = 92 个节点挤在屏上，手机上点不准也读不清）
    if state["rendered"] <= 0:
        problems.append("R7 首屏画布上一个节点都没有（rendered = %d）" % state["rendered"])
    elif state["nodes"] > 0 and state["rendered"] >= state["nodes"]:
        problems.append("R7 首屏把全部 %d 个节点一次铺满了 —— 「点选逐步延展」没生效"
                        % state["nodes"])

    # R8 · 节点操作三件套（展开 / 锁定 / 关闭）在页面上
    if not state["actions"]:
        problems.append("R8 详情卡里没有「展开 / 锁定 / 关闭」三个按钮"
                        " —— 画布退化成只能看，不能一层层展开")

    return problems, ""


def _file_uri(path):
    return pathlib.Path(path).resolve().as_uri()


def check_render_mobile(index_path, timeout_ms=RENDER_TIMEOUT_MS):
    """移动端列表视图检查 —— 真跑一次 390×844。

    断言：页面无未捕获异常 · 遮罩已隐藏 · **列表视图可见且有内容** ·
          **画布视图不可见**（手机上默认走卡片流，画布是「全景图」那一层）·
          分类卡数量 > 0（分类卡流真的渲染出来了）。

    为什么单列一层：桌面 1440×900 那次渲染**全绿也不代表手机能用** ——
    手机上默认形态是卡片流，这条断言只在这里才成立。
    """
    try:
        from playwright.sync_api import sync_playwright
    except Exception as e:
        return [], "跳过（本机没有 playwright：%s）" % e

    problems = []
    errors = []

    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch()
            try:
                page = browser.new_page(viewport=dict(MOBILE_VIEWPORT))
                page.on("pageerror", lambda e: errors.append("未捕获异常：%s" % e))
                page.on("console", lambda m: errors.append("console.error：%s" % m.text)
                        if m.type == "error" else None)
                page.goto(_file_uri(index_path))
                try:
                    page.wait_for_function(
                        "() => { const e = document.getElementById('loading');"
                        " return !e || getComputedStyle(e).display === 'none'; }",
                        timeout=timeout_ms)
                    loading_hidden = True
                except Exception:
                    loading_hidden = False
                page.wait_for_timeout(600)
                state = page.evaluate("""() => {
                    const vl = document.getElementById('viewList');
                    const vg = document.getElementById('viewGraph');
                    const l = document.getElementById('loading');
                    const cs = vl ? getComputedStyle(vl) : null;
                    const gs = vg ? getComputedStyle(vg) : null;
                    return {
                        view: document.body.getAttribute('data-view'),
                        listVisible: cs ? (cs.visibility === 'visible' && cs.display !== 'none') : false,
                        listCats: document.querySelectorAll('#lgCats .cat').length,
                        listUrgent: document.querySelectorAll('#lgUrgent .u-item').length,
                        listRows: document.querySelectorAll('#lgResults .row').length,
                        graphVisible: gs ? (gs.visibility === 'visible') : false,
                        loading: l ? getComputedStyle(l).display : 'missing',
                        nodes: window.KG_GRAPH ? (window.KG_GRAPH.nodes || []).length : -1,
                        patient: typeof window.KG_PATIENT
                    };
                }""")
            finally:
                browser.close()
    except Exception as e:
        return [], "跳过（playwright 起不来：%s）" % e

    # M1 · 页面级错误
    for msg in errors:
        problems.append("M1 页面报错：%s" % msg)

    # M2 · 手机默认走列表视图
    if state["view"] != "list":
        problems.append("M2 手机视口下默认视图不是「知识浏览」（body[data-view] = %r）"
                        " —— 手机首屏应该是卡片流，不是画布" % state["view"])

    # M3 · 列表视图可见
    if not state["listVisible"]:
        problems.append("M3 列表视图不可见（#viewList 的 visibility 不是 visible）"
                        " —— 手机上用户看到的是空白")

    # M4 · 画布视图应当隐藏（它是「全景图」那一层，不是首屏）
    if state["graphVisible"]:
        problems.append("M4 画布视图在手机首屏仍然可见 —— 两层叠在一起会互相挡")

    # M5 · 分类卡流真的渲染出来了
    if state["listCats"] < 1:
        problems.append("M5 列表里一个分类卡都没有（#lgCats .cat = %d）"
                        " —— 卡片流没渲染出来" % state["listCats"])

    # M6 · 首屏遮罩已隐藏
    if not loading_hidden or state["loading"] != "none":
        problems.append("M6 首屏遮罩没隐藏（#loading 的 display = %s）"
                        " —— 手机上看到的就是「一直转圈圈」" % state["loading"])

    return problems, ""


def check_render_triples(triples_path, expect_rows=0, timeout_ms=RENDER_TIMEOUT_MS):
    """三元组页渲染检查 —— 真跑一次浏览器

    断言：页面无未捕获异常 · 数据已装载（window.KG_TRIPLES 非空）·
          **表格里真的渲染出了行**（不是空表）· 行数与数据一致（截断上限内）。

    为什么单列一层：这个页面是**客户直接打开看的表** —— 空表比不提供这个页面更糟
    （客户会说「表是空的」）。闸门必须能抓到「数据没装上」和「渲染没跑」。
    """
    try:
        from playwright.sync_api import sync_playwright
    except Exception as e:
        return [], "跳过（本机没有 playwright：%s）" % e

    problems = []
    errors = []
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch()
            try:
                page = browser.new_page(viewport={"width": 1440, "height": 900})
                page.on("pageerror", lambda e: errors.append("未捕获异常：%s" % e))
                page.on("console", lambda m: errors.append("console.error：%s" % m.text)
                        if m.type == "error" else None)
                page.goto(_file_uri(triples_path))
                page.wait_for_timeout(900)
                state = page.evaluate("""() => {
                    const D = window.KG_TRIPLES || {rows: [], labels: {}};
                    const rows = D.rows || [];
                    const cell = document.querySelector('#tb tr td');
                    return {
                        dataRows: rows.length,
                        firstRow: rows.length ? rows[0] : null,
                        firstRowCols: rows.length ? rows[0].length : 0,
                        domRows: document.querySelectorAll('#tb tr').length,
                        meta: (document.getElementById('meta')||{}).textContent || '',
                        csvHref: (document.getElementById('dl')||{}).getAttribute('href') || '',
                        labelCount: Object.keys(D.labels || {}).length,
                        firstTypeText: cell ? cell.textContent.trim() : '',
                        firstTypeTitle: cell ? (cell.getAttribute('title') || '') : ''
                    };
                }""")
            finally:
                browser.close()
    except Exception as e:
        return [], "跳过（playwright 起不来：%s）" % e

    for msg in errors:
        problems.append("T1 页面报错：%s" % msg)

    if state["dataRows"] <= 0:
        problems.append("T2 三元组数据是空的（window.KG_TRIPLES = %d 行）"
                        " —— 表页会显示成空表" % state["dataRows"])
    if state["firstRowCols"] != 5:
        problems.append("T3 三元组每行不是 5 列（实际 %d 列）" % state["firstRowCols"])
    if state["domRows"] <= 0:
        problems.append("T4 表格里一行都没渲染出来（#tb tr = %d）" % state["domRows"])
    if state["domRows"] > 0 and state["dataRows"] > 0:
        # 页面上限 5000 行；数据更多时只显示前 5000 行 ⇒ 只能对「不超过上限」的情况查等号
        if state["dataRows"] <= 5000 and state["domRows"] != state["dataRows"]:
            problems.append("T5 页面渲染 %d 行，但数据有 %d 行 —— 对不上"
                            % (state["domRows"], state["dataRows"]))
    if expect_rows and state["dataRows"] != expect_rows:
        problems.append("T6 三元组行数 %d ≠ 5 列表行数 %d" % (state["dataRows"], expect_rows))
    if "csv" not in (state["csvHref"] or "").lower():
        problems.append("T7 下载 CSV 的链接没指向 CSV（href = %r）" % state["csvHref"])
    # T8 · 类型列显示的应是**中文标签**，不是英文 key（英文 key 留在 title 里）
    if state["labelCount"] <= 0:
        problems.append("T8 类型中文标签表是空的 —— 类型列会显示成 SymptomSign 这类英文 key")
    elif state["firstTypeText"] and state["firstTypeText"] == state["firstTypeTitle"]:
        problems.append("T9 类型列显示的还是英文 key（%r）—— 客户端读不懂" % state["firstTypeText"])

    return problems, ""


def check_text_files_clean(out_dir, topic_key):
    """产出目录里的**文本文件**不得含 NUL 字节 —— 返回问题清单（空 = 通过）

    为什么单独查数据文件：`check_html_static` 只查页面；`data/*.js` / `*.json` / `*.csv`
    是同一类脏字节的落点（模板里的一个坏字符会被原样写进产物）。
    判据 = 文件前 64 KiB 里出现 NUL ⇒ 报出来（NUL 出现得再晚也报）。
    """
    problems = []
    text_ext = (".html", ".js", ".json", ".csv", ".md", ".txt", ".py", ".cypher")
    for root, dirs, files in os.walk(out_dir):
        dirs.sort()
        for fn in sorted(files):
            if not fn.lower().endswith(text_ext):
                continue
            p = os.path.join(root, fn)
            try:
                with open(p, "rb") as f:
                    blob = f.read()
            except Exception as e:
                problems.append("读不了 %s：%s" % (os.path.relpath(p, out_dir), e))
                continue
            n = blob.count(b"\x00")
            if n:
                problems.append("%s 里有 %d 个 NUL 字节 —— git 会把它判成二进制"
                                % (os.path.relpath(p, out_dir).replace("\\", "/"), n))
    return problems


def structure_gate(index_path, do_render=True, do_js=True):
    """对产出页面跑完整结构闸门。

    返回 (问题清单, [(层名, 结论)]) —— 结论含「通过」与「跳过（原因）」。
    """
    with open(index_path, "r", encoding="utf-8") as f:
        html = f.read()

    problems = []
    notes = []

    static_problems = check_html_static(html)
    problems.extend(static_problems)
    notes.append(("S · 静态结构（标签配平 / 裸标签字面量 / 必备锚点）",
                   "通过" if not static_problems else "不通过（%d 项）" % len(static_problems)))

    if do_js:
        js_problems, js_skip = check_js_syntax(html)
        problems.extend(js_problems)
        notes.append(("J · JS 语法（node --check 内联脚本）",
                       "通过" if not js_problems else ("不通过（%d 项）" % len(js_problems)
                                                      if not js_skip else js_skip)))
        if js_skip:
            notes[-1] = ("J · JS 语法（node --check 内联脚本）", js_skip)
    else:
        notes.append(("J · JS 语法（node --check 内联脚本）", "跳过（命令行显式关闭）"))

    if do_render:
        render_problems, render_skip = check_render(index_path)
        problems.extend(render_problems)
        notes.append(("R · 首屏渲染（playwright 1440×900 真跑一次）",
                       "通过" if not render_problems else ("不通过（%d 项）" % len(render_problems)
                                                          if not render_skip else render_skip)))
        if render_skip:
            notes[-1] = ("R · 首屏渲染（playwright 1440×900 真跑一次）", render_skip)

        mob_problems, mob_skip = check_render_mobile(index_path)
        problems.extend(mob_problems)
        notes.append(("M · 移动端列表视图（playwright 390×844 真跑一次）",
                       "通过" if not mob_problems else ("不通过（%d 项）" % len(mob_problems)
                                                       if not mob_skip else mob_skip)))
        if mob_skip:
            notes[-1] = ("M · 移动端列表视图（playwright 390×844 真跑一次）", mob_skip)
    else:
        notes.append(("R · 首屏渲染（playwright 1440×900 真跑一次）", "跳过（命令行显式关闭）"))
        notes.append(("M · 移动端列表视图（playwright 390×844 真跑一次）", "跳过（命令行显式关闭）"))

    return problems, notes


# --------------------------------------------------------------------------
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
    ap.add_argument("--no-render-check", action="store_true",
                    help="关掉首屏渲染检查（默认跑；关掉会打印说明）")
    ap.add_argument("--no-js-check", action="store_true",
                    help="关掉内联脚本的 JS 语法检查（默认跑；关掉会打印说明）")
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
    gate_problems = []
    for tk, p in topic_of.items():
        d = datas.get(tk)
        if d is None:
            continue
        try:
            out_dir, triples_rows = build_one(tk, d, p, out_root, rep, terms_source)
        except StructureGateError as e:
            print("\n⛔ 结构闸门不通过 —— 已中止构建：\n%s" % e)
            return 1
        print("   %s" % out_dir)
        # ---- 结构闸门：对**写盘后的真实产物**再查一遍（JS 语法 + 首屏渲染）
        index_path = os.path.join(out_dir, "index.html")
        probs, notes = structure_gate(index_path,
                                       do_render=not args.no_render_check,
                                       do_js=not args.no_js_check)
        print("   结构闸门（%s）" % index_path)
        for nm, verdict in notes:
            print("      · %-42s %s" % (nm, verdict))
        if probs:
            print("      ⛔ 不通过项：")
            for pb in probs:
                print("        · %s" % pb)
            gate_problems.extend(probs)

        # ---- 结构闸门：三元组表页（客户直接打开看的那张表）
        triples_path = os.path.join(out_dir, "triples.html")
        if os.path.exists(triples_path):
            t_probs, t_skip = check_render_triples(triples_path, expect_rows=triples_rows)
            print("   结构闸门（%s）" % triples_path)
            print("      · %-42s %s" % (
                "T · 三元组表页渲染（真跑一次）",
                "通过" if not t_probs else ("不通过（%d 项）" % len(t_probs)
                                           if not t_skip else t_skip)))
            if t_probs:
                for pb in t_probs:
                    print("        · %s" % pb)
                gate_problems.extend(t_probs)
        else:
            print("   结构闸门（%s）" % triples_path)
            print("      · %-42s %s" % ("T · 三元组表页渲染（真跑一次）",
                                        "跳过（目录里没有 triples.html）"))

        # ---- 结构闸门：产出目录里的文本文件不得含 NUL 字节
        nul_problems = check_text_files_clean(out_dir, tk)
        print("      · %-42s %s" % (
            "N · 文本文件无 NUL 字节（git 不判二进制）",
            "通过" if not nul_problems else "不通过（%d 项）" % len(nul_problems)))
        for pb in nul_problems:
            print("        · %s" % pb)
        gate_problems.extend(nul_problems)
    if gate_problems:
        print("\n⛔ 结构闸门未通过（%d 项）—— **本次产出不可交付**" % len(gate_problems))
        return 1
    print("\n✅ 完成")
    return 0 if nf == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
