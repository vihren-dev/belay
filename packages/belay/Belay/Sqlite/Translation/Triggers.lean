import Belay.Sqlite.Translation.Writes

set_option doc.verso true

/-! CREATE TRIGGER. The port of {lit}`belay/sqlite/syntax_triggers.py`: a trigger keeps its
name, {lit}`IF NOT EXISTS`, its time, its event, its table, its {lit}`WHEN` condition and its
body statements, each with the fields of its {lit}`Syntax.BodyStatement` constructor. -/

namespace Belay.Sqlite.Translation

/-- The refusal of a subquery in {lit}`WHEN`. -/
def inWhen : String :=
  "A subquery in the WHEN condition of a trigger is not modeled; move the test into the trigger's statements"

/-- The body statement constructor with every field, the {lit}`subqueries` field included; unlike
a statement, a body statement omits no field. -/
def bodyStatement (kind : String) (fields : Array (String × Located)) (items : Array Located) (node : ParseNode)
    (after : Array (String × Located) := #[]) : Located :=
  constructor kind (fields ++ #[("subqueries", sequence items node.start node.stop)] ++ after) node.start node.stop

/-- The table of a body statement, a {lit}`trnm` node; a qualified name is refused, as SQLite
refuses it inside a trigger. -/
def bodyTable (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  unless tree.symbols node == ["nm"] do
    unsupported node "A qualified table name is not allowed in a trigger; write the table name"
  plainName tree (tree.children node)[0]!

/-- The optional WHERE filter of a {lit}`where_opt` node, a null leaf without it. -/
def bodyFilter (tree : SqlTree) (whereNode : ParseNode) : TranslateM Located := do
  let parts := tree.children whereNode
  if parts.isEmpty then return leaf .null whereNode.start whereNode.stop
  queryExpression tree parts[1]!

/-- {lit}`INSERT [OR algorithm] INTO table [(columns)] VALUES rows [ON CONFLICT ...]` and
{lit}`REPLACE INTO` in a trigger body. -/
def bodyInsert (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  let parts ← require tree node ["scanpt", "insert_cmd", "INTO", "trnm", "idlist_opt", "select", "upsert", "scanpt"]
  let (conflicts, returned) ← noSubqueries
    "A subquery in ON CONFLICT is not modeled; read the value in a separate statement" (conflictClauses tree parts[6]!)
  unless returned.isEmpty do unsupported parts[6]! "RETURNING is not allowed in a trigger; remove it"
  let columns ← columnList tree parts[4]!
  let (rows, items) ← statementSubqueries (valueRows tree parts[5]!)
  let table ← bodyTable tree parts[3]!
  return bodyStatement "insert" #[("table", table), ("columns", columns), ("rows", rows), ("conflicts", conflicts),
    ("algorithm", ← insertAlgorithm tree parts[1]!)] items node

/-- {lit}`UPDATE table SET assignments [WHERE expression]` in a trigger body. -/
def bodyUpdate (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  let parts ← require tree node ["UPDATE", "orconf", "trnm", "tridxby", "SET", "setlist", "from", "where_opt", "scanpt"]
  absent parts[1]! "An OR conflict clause of UPDATE"
  absent parts[3]! "INDEXED BY"
  absent parts[6]! "UPDATE FROM"
  let ((mapped, filter), items) ← statementSubqueries do
    let mapped ← assignmentList tree parts[5]!
    return (mapped, ← bodyFilter tree parts[7]!)
  return bodyStatement "update" #[("table", ← bodyTable tree parts[2]!), ("assignments", mapped), ("filter", filter)]
    items node

/-- {lit}`DELETE FROM table [WHERE expression]` in a trigger body. -/
def bodyDelete (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  let parts ← require tree node ["DELETE", "FROM", "trnm", "tridxby", "where_opt", "scanpt"]
  absent parts[3]! "INDEXED BY"
  let (filter, items) ← statementSubqueries (bodyFilter tree parts[4]!)
  return bodyStatement "delete" #[("table", ← bodyTable tree parts[2]!), ("filter", filter)] items node

/-- A SELECT in a trigger body, with every clause of {lit}`Syntax.BodyStatement.select`. -/
def bodySelect (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  let parts ← require tree node ["scanpt", "select", "scanpt"]
  let (clauses, items) ← statementSubqueries (queryClauses tree parts[1]!)
  return bodyStatement "select" (clauses.extract 0 8) items node (clauses.extract 8 clauses.size)

/-- The statements of a {lit}`trigger_cmd_list` node in text order. -/
def body (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  let items ← leftList tree node [(2, ["trigger_cmd", "SEMI"]), (3, ["trigger_cmd_list", "trigger_cmd", "SEMI"])]
  let statements ← items.mapM fun item => do
    let command := fromEnd item 2
    let symbols := tree.symbols command
    match symbols.head? with
    | some "UPDATE" => bodyUpdate tree command
    | some "DELETE" => bodyDelete tree command
    | _ => if (symbols.drop 1).take 1 == ["insert_cmd"] then bodyInsert tree command else bodySelect tree command
  return sequence statements node.start node.stop

/-- {lit}`before` for BEFORE and for a trigger without a time, {lit}`after` for AFTER; INSTEAD OF,
which needs a view, is refused. -/
def triggerTime (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  let symbols := tree.symbols node
  if symbols == ["INSTEAD", "OF"] then
    unsupported node ("INSTEAD OF triggers are not modeled, as the model has no views; " ++
      "write the statements on the tables instead")
  return leaf (if symbols == ["AFTER"] then "after" else "before") node.start node.stop

/-- {lit}`insert`, {lit}`delete`, or {lit}`update` with the column names of {lit}`UPDATE OF`. -/
def triggerEvent (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  let parts := tree.children node
  match tree.symbols node with
  | ["INSERT"] => return leaf "insert" node.start node.stop
  | ["DELETE"] => return leaf "delete" node.start node.stop
  | symbols =>
    let columns ← if symbols == ["UPDATE", "OF", "idlist"] then do
        let items ← leftList tree parts[2]! [(1, ["nm"]), (3, ["idlist", "COMMA", "nm"])]
        items.mapM fun item => plainName tree (last item)
      else pure #[]
    return constructor "update" #[("columns", sequence columns node.start node.stop)] node.start node.stop

/-- {lit}`CREATE TRIGGER [IF NOT EXISTS] name [BEFORE|AFTER] event ON table [FOR EACH ROW]
[WHEN condition] BEGIN statements END`. -/
def createTrigger (tree : SqlTree) (command : ParseNode) : TranslateM Located := do
  let parts := tree.children command
  let declaration ← require tree parts[1]! ["temp", "TRIGGER", "ifnotexists", "nm", "dbnm", "trigger_time",
    "trigger_event", "ON", "fullname", "foreach_clause", "when_clause"]
  absent declaration[0]! "A TEMP trigger"
  absent declaration[4]! "A schema name"
  let table := declaration[8]!
  unless tree.symbols table == ["nm"] do unsupported table "A schema name is not modeled; remove it"
  let whenNode := declaration[10]!
  let condition ← noSubqueries inWhen do
    if whenNode.children.isEmpty then pure (leaf .null whenNode.start whenNode.stop)
    else queryExpression tree (tree.children whenNode)[1]!
  let existsNode := declaration[2]!
  let triggerName ← plainName tree declaration[3]!
  let time ← triggerTime tree declaration[5]!
  let event ← triggerEvent tree declaration[6]!
  let tableName ← plainName tree (tree.children table)[0]!
  return constructor "createTrigger" #[("name", triggerName),
    ("ifNotExists", leaf (!existsNode.children.isEmpty) existsNode.start existsNode.stop), ("time", time), ("event", event),
    ("table", tableName), ("condition", condition), ("body", ← body tree parts[3]!)] command.start command.stop

end Belay.Sqlite.Translation
