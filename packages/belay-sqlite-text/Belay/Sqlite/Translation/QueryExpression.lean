import Belay.Sqlite.Translation.Queries
import Belay.Sqlite.Translation.NameTokens

set_option doc.verso true

/-! The {lit}`expr` productions of a query, and result columns. The port of
{lit}`query_expression`, {lit}`result_column` and {lit}`result_columns` of
{lit}`belay/sqlite/syntax_queries.py`. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- Map an {lit}`expr` production of a query, or refuse it with its range; operands and nested
queries go through the mappers. -/
def queryExpressionWith (mappers : Mappers) (tree : SqlTree) (node : ParseNode) : TranslateM (Located Syntax.Expr) := do
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
    let collation ← identifierName tree parts[2]!
    return composite (.collate operand.value collation.value) node.start node.stop #[operand.span, collation.span]
  | ["expr", "IS", "NOT", "expr"] => operation mappers tree node (.compare .isNot) parts[0]! parts[3]!
  | ["MINUS", "expr"] => unary mappers tree node .negate parts[1]!
  | ["PLUS", "expr"] => unary mappers tree node .positive parts[1]!
  | ["CAST", "LP", "expr", "AS", "typetoken", "RP"] => do
    let operand ← mappers.expression tree parts[2]!
    return composite (.cast operand.value (tree.text parts[4]!)) node.start node.stop #[operand.span, spanOf parts[4]!]
  | ["nm", "DOT", "nm"] => do
    let source ← identifierName tree parts[0]!
    let column ← identifierName tree parts[2]!
    return composite (.qualified source.value column.value) node.start node.stop
      #[source.span, column.span, (missing node.start node.stop : Located (Option Identifier)).span]
  | ["nm", "DOT", "nm", "DOT", "nm"] => do
    let schema ← identifierName tree parts[0]!
    unless schema.value.isInitialSchema do
      unsupported node "A schema-qualified column is not modeled; write source.column"
    let source ← identifierName tree parts[2]!
    let column ← identifierName tree parts[4]!
    return composite (.qualified source.value column.value (some schema.value)) node.start node.stop
      #[source.span, column.span, schema.span]
  | ["NOT", "expr"] => unary mappers tree node .not parts[1]!
  | ["expr", "ISNULL"] | ["expr", "NOTNULL"] | ["expr", "NOT", "NULL"] => do
    let operand ← mappers.expression tree parts[0]!
    return composite (.isNull operand.value (symbols[1]! != "ISNULL")) node.start node.stop #[operand.span, spanOf node]
  | "ID" :: "LP" :: _ | "LIKE_KW" :: "LP" :: _ | "IF" :: "LP" :: _ | "REPLACE" :: "LP" :: _ =>
    functionCall mappers tree node parts
  | ["expr", "likeop", "expr"] | ["expr", "likeop", "expr", "ESCAPE", "expr"] => like mappers tree node parts
  | ["RAISE", "LP", "IGNORE", "RP"] => raiseForm mappers tree node parts true
  | ["RAISE", "LP", "raisetype", "COMMA", "expr", "RP"] => raiseForm mappers tree node parts false
  | _ => expression tree node

/-- The alias of an {lit}`as` node: {lit}`AS name`, a bare name, or none. -/
def alias (tree : SqlTree) (node : ParseNode) : TranslateM (Located (Option Identifier)) := do
  let parts := tree.children node
  if tree.symbols node == ["AS", "nm"] then return (← identifierName tree parts[1]!).present
  if h : 0 < parts.size then
    return { value := some (Identifier.ofString (dequote (tree.text parts[0]))), span := nameSpanOf node }
  return missing node.start node.stop

/-- {lit}`*`, {lit}`source.*`, or an expression with its optional alias and its text, which SQLite
uses as the column's name. -/
def resultColumn (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) :
    TranslateM (Located Syntax.ResultColumn) := do
  match parts.toList.map (·.symbol) with
  | ["scanpt", "STAR"] => return leaf .star parts[1]!.start parts[1]!.stop
  | ["scanpt", "nm", "DOT", "STAR"] =>
    let source ← identifierName tree parts[1]!
    return composite (.sourceStar source.value) parts[1]!.start parts[3]!.stop #[source.span]
  | ["scanpt", "expr", "scanpt", "as"] =>
    let named ← alias tree parts[3]!
    let value := parts[1]!
    let firstSubquery ← subqueryCount
    let mapped ← mappers.expression tree value
    let tokens ← if (← get).nameTokens then expressionNameTokens tree value.start value.stop mapped.span firstSubquery
      else pure []
    return composite (.expression mapped.value named.value { text := tree.text value, tokens }) value.start
      (max value.stop parts[3]!.stop)
      #[mapped.span, named.span, spanOf value]
  | _ => unsupported node "Only `*` and expressions are modeled as result columns; write the column names"

/-- The result columns of a {lit}`selcollist` node in text order. Like the Python translation, it
maps them from the last to the first. -/
def resultColumns (mappers : Mappers) (tree : SqlTree) (node : ParseNode) :
    TranslateM (Located (List Syntax.ResultColumn)) := do
  let mut items : Array (Located Syntax.ResultColumn) := #[]
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
