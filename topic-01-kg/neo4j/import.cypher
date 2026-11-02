// ===========================================================================
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
