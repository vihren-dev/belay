import Belay.Sqlite.Translation.Queries

set_option doc.verso true

/-! The {lit}`expr` productions of a query, and result columns. The port of
{lit}`query_expression`, {lit}`result_column` and {lit}`result_columns` of
{lit}`belay/sqlite/syntax_queries.py`. -/

namespace Belay.Sqlite.Translation

/-- Map an {lit}`expr` production of a query, or refuse it with its range; operands and nested
queries go through the mappers. -/
def queryExpressionWith (mappers : Mappers) (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  let parts := tree.children node
  let symbols := tree.symbols node
  if symbols == ["LP", "expr", "RP"] then return ← mappers.expression tree parts[1]!
  if let some form ← subqueryForm mappers tree node parts symbols then return form
  if let some form ← listForm mappers tree node parts symbols then return form
  if let [first, operator, third] := symbols then
    if first == "expr" && third == "expr" then
      if let some form := binaryForm mappers tree node parts operator then return ← form
  match symbols with
  | ["expr", "PTR", "expr"] =>
    call mappers tree node.start node.stop (leaf (tree.text parts[1]!) parts[1]!.start parts[1]!.stop)
      #[parts[0]!, parts[2]!]
  | ["expr", "COLLATE", "ID"] | ["expr", "COLLATE", "STRING"] => do
    let operand ← mappers.expression tree parts[0]!
    return constructor "collate" #[("operand", operand), ("name", ← plainName tree parts[2]!)] node.start node.stop
  | ["expr", "IS", "NOT", "expr"] => operation mappers tree node "compare" "isNot" parts[0]! parts[3]!
  | ["MINUS", "expr"] => unary mappers tree node "negate" parts[1]!
  | ["PLUS", "expr"] => unary mappers tree node "positive" parts[1]!
  | ["CAST", "LP", "expr", "AS", "typetoken", "RP"] => do
    let operand ← mappers.expression tree parts[2]!
    return constructor "cast" #[("operand", operand),
      ("typeName", leaf (tree.text parts[4]!) parts[4]!.start parts[4]!.stop)] node.start node.stop
  | ["nm", "DOT", "nm"] => do
    let source ← plainName tree parts[0]!
    return constructor "qualified" #[("source", source), ("column", ← plainName tree parts[2]!)] node.start node.stop
  | ["nm", "DOT", "nm", "DOT", "nm"] => unsupported node "A schema-qualified column is not modeled; write source.column"
  | ["NOT", "expr"] => unary mappers tree node "not" parts[1]!
  | ["expr", "ISNULL"] | ["expr", "NOTNULL"] | ["expr", "NOT", "NULL"] => do
    let operand ← mappers.expression tree parts[0]!
    return constructor "isNull" #[("operand", operand), ("negated", leaf (symbols[1]! != "ISNULL") node.start node.stop)]
      node.start node.stop
  | "ID" :: "LP" :: _ | "LIKE_KW" :: "LP" :: _ | "IF" :: "LP" :: _ | "REPLACE" :: "LP" :: _ =>
    functionCall mappers tree node parts
  | ["expr", "likeop", "expr"] | ["expr", "likeop", "expr", "ESCAPE", "expr"] => like mappers tree node parts
  | ["RAISE", "LP", "IGNORE", "RP"] => raiseForm mappers tree node parts true
  | ["RAISE", "LP", "raisetype", "COMMA", "expr", "RP"] => raiseForm mappers tree node parts false
  | _ => expression tree node

/-- The alias of an {lit}`as` node: {lit}`AS name`, a bare name, or none. -/
def alias (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  let parts := tree.children node
  if tree.symbols node == ["AS", "nm"] then return ← plainName tree parts[1]!
  if h : 0 < parts.size then return leaf (dequote (tree.text parts[0])) node.start node.stop
  return leaf .null node.start node.stop

/-- {lit}`*`, {lit}`source.*`, or an expression with its optional alias and its text, which SQLite
uses as the column's name. -/
def resultColumn (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) :
    TranslateM Located := do
  match parts.toList.map (·.symbol) with
  | ["scanpt", "STAR"] => return leaf "star" parts[1]!.start parts[1]!.stop
  | ["scanpt", "nm", "DOT", "STAR"] =>
    return constructor "sourceStar" #[("source", ← plainName tree parts[1]!)] parts[1]!.start parts[3]!.stop
  | ["scanpt", "expr", "scanpt", "as"] =>
    let named ← alias tree parts[3]!
    let value := parts[1]!
    return constructor "expression" #[("value", ← mappers.expression tree value), ("alias", named),
      ("text", leaf (tree.text value) value.start value.stop)] value.start (max value.stop parts[3]!.stop)
  | _ => unsupported node "Only `*` and expressions are modeled as result columns; write the column names"

/-- The result columns of a {lit}`selcollist` node in text order. Like the Python translation, it
maps them from the last to the first. -/
def resultColumns (mappers : Mappers) (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  let mut items : Array Located := #[]
  let mut current := node
  let mut fuel := tree.nodes.size + 1
  while fuel > 0 do
    fuel := fuel - 1
    let parts := tree.children current
    items := items.push (← resultColumn mappers tree current (parts.extract 1 parts.size))
    if parts[0]!.children.isEmpty then break
    current := (← require tree parts[0]! ["selcollist", "COMMA"])[0]!
  return sequence items.reverse node.start node.stop

end Belay.Sqlite.Translation
