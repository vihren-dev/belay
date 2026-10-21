import Belay.Sqlite.Translation.Conflicts

set_option doc.verso true

/-! Transaction control, INSERT, UPDATE and DELETE. The port of
{lit}`belay/sqlite/syntax_writes.py`: each write keeps its RETURNING columns and the subqueries
of its values, assignments and filter; a subquery in RETURNING or ON CONFLICT is refused. -/

namespace Belay.Sqlite.Translation

/-- The refusal of a subquery in RETURNING or ON CONFLICT. -/
def inWriteClause : String := "A subquery in RETURNING or ON CONFLICT is not modeled; read the value in a separate statement"

/-- {lit}`BEGIN [DEFERRED] [TRANSACTION]`, {lit}`COMMIT` or {lit}`END [TRANSACTION]`, and
{lit}`ROLLBACK [TRANSACTION]`. -/
def transaction (tree : SqlTree) (command : ParseNode) : TranslateM Located := do
  let keyword := (tree.children command)[0]!.symbol
  let option ← if keyword == "BEGIN" then do
      let parts ← require tree command ["BEGIN", "transtype", "trans_opt"]
      unless tree.symbols parts[1]! == [] || tree.symbols parts[1]! == ["DEFERRED"] do
        unsupported parts[1]! "Only deferred transactions are modeled; write BEGIN or BEGIN DEFERRED"
      pure parts[2]!
    else pure (← require tree command [keyword, "trans_opt"])[1]!
  unless tree.symbols option == [] || tree.symbols option == ["TRANSACTION"] do
    unsupported option "Named transactions are not modeled; remove the transaction name"
  let kind := match keyword with | "BEGIN" => "begin" | "ROLLBACK" => "rollback" | _ => "commit"
  return leaf kind command.start command.stop

/-- The VALUES rows of an INSERT source in text order; a SELECT source is refused. -/
def valueRows (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  let selectNode := (← require tree node ["selectnowith"])[0]!
  let one := (← require tree selectNode ["oneselect"])[0]!
  unless tree.symbols one == ["values"] || tree.symbols one == ["mvalues"] do
    unsupported one "Only VALUES rows are modeled as an INSERT source; write INSERT ... VALUES (...)"
  let mut current := (tree.children one)[0]!
  let mut listed : Array ParseNode := #[]
  let mut fuel := tree.nodes.size + 1
  while current.symbol == "mvalues" && fuel > 0 do
    fuel := fuel - 1
    let earlier := ((tree.children current)[0]?.map (·.symbol)).getD ""
    let parts ← require tree current [earlier, "COMMA", "LP", "nexprlist", "RP"]
    listed := listed.push parts[3]!
    current := parts[0]!
  listed := listed.push (← require tree current ["VALUES", "LP", "nexprlist", "RP"])[2]!
  let rows ← listed.reverse.mapM fun row => do
    let items ← leftList tree row [(1, ["expr"]), (3, ["nexprlist", "COMMA", "expr"])]
    return sequence (← items.mapM fun item => queryExpression tree (last item)) row.start row.stop
  return sequence rows node.start node.stop

/-- The {lit}`returning` field of a write: the result columns of the parts
{lit}`RETURNING selcollist`, or an empty list without them. -/
def returning (tree : SqlTree) (command : ParseNode) (parts : Array ParseNode) : TranslateM Located := do
  if parts.isEmpty then return sequence #[] command.stop command.stop
  noSubqueries inWriteClause (resultColumns queryMappers tree parts[1]!)

/-- The column list of an {lit}`idlist_opt` node, or none. -/
def columnList (tree : SqlTree) (columns : ParseNode) : TranslateM Located := do
  if columns.children.isEmpty then return leaf .null columns.start columns.stop
  let listed := (← require tree columns ["LP", "idlist", "RP"])[1]!
  let items ← leftList tree listed [(1, ["nm"]), (3, ["idlist", "COMMA", "nm"])]
  return sequence (← items.mapM fun item => plainName tree (last item)) columns.start columns.stop

/-- {lit}`INSERT [OR algorithm] INTO table [(columns)] VALUES rows [ON CONFLICT ...] [RETURNING columns]`,
and {lit}`REPLACE INTO`. -/
def insert (tree : SqlTree) (command : ParseNode) : TranslateM Located := do
  let parts ← require tree command ["with", "insert_cmd", "INTO", "xfullname", "idlist_opt", "select", "upsert"]
  absent parts[0]! "A WITH clause"
  let algorithm ← insertAlgorithm tree parts[1]!
  let (conflicts, returned) ← noSubqueries inWriteClause (conflictClauses tree parts[6]!)
  let table := (← require tree parts[3]! ["nm"])[0]!
  let columns ← columnList tree parts[4]!
  let (rows, items) ← statementSubqueries (valueRows tree parts[5]!)
  let tableName ← plainName tree table
  return withSubqueries "insert" #[("table", tableName), ("columns", columns), ("rows", rows),
    ("conflicts", conflicts), ("algorithm", algorithm), ("returning", ← returning tree command returned)]
    items command.start command.stop

/-- The optional WHERE filter and the {lit}`RETURNING selcollist` parts of a
{lit}`where_opt_ret` node, which UPDATE and DELETE share; a missing filter is a null leaf. -/
def filterAndReturning (tree : SqlTree) (whereNode : ParseNode) (statement : String) :
    TranslateM (Located × Array ParseNode) := do
  let parts := tree.children whereNode
  let symbols := tree.symbols whereNode
  unless [[], ["WHERE", "expr"], ["RETURNING", "selcollist"], ["WHERE", "expr", "RETURNING", "selcollist"]].contains symbols do
    unsupported whereNode s!"Unsupported {statement} clause; write [WHERE expression] [RETURNING columns]"
  let filter ← if symbols.take 1 == ["WHERE"] then queryExpression tree parts[1]!
    else pure (leaf .null whereNode.start whereNode.stop)
  let returned := if symbols.drop (symbols.length - 2) == ["RETURNING", "selcollist"] then
    parts.extract (parts.size - 2) parts.size else #[]
  return (filter, returned)

/-- {lit}`UPDATE table SET assignments [WHERE expression] [RETURNING columns]`. -/
def update (tree : SqlTree) (command : ParseNode) : TranslateM Located := do
  let parts ← require tree command ["with", "UPDATE", "orconf", "xfullname", "indexed_opt", "SET", "setlist", "from",
    "where_opt_ret"]
  absent parts[0]! "A WITH clause"
  absent parts[2]! "An OR conflict clause"
  absent parts[4]! "INDEXED BY"
  absent parts[7]! "UPDATE FROM"
  let table := (← require tree parts[3]! ["nm"])[0]!
  let ((mapped, filter, returned), items) ← statementSubqueries do
    let mapped ← assignmentList tree parts[6]!
    let (filter, returned) ← filterAndReturning tree parts[8]! "UPDATE"
    return (mapped, filter, returned)
  let tableName ← plainName tree table
  return withSubqueries "update" #[("table", tableName), ("assignments", mapped), ("filter", filter),
    ("returning", ← returning tree command returned)] items command.start command.stop

/-- {lit}`DELETE FROM table [WHERE expression] [RETURNING columns]`. -/
def delete (tree : SqlTree) (command : ParseNode) : TranslateM Located := do
  let parts ← require tree command ["with", "DELETE", "FROM", "xfullname", "indexed_opt", "where_opt_ret"]
  absent parts[0]! "A WITH clause"
  absent parts[4]! "INDEXED BY"
  let table := (← require tree parts[3]! ["nm"])[0]!
  let ((filter, returned), items) ← statementSubqueries (filterAndReturning tree parts[5]! "DELETE")
  let tableName ← plainName tree table
  return withSubqueries "delete" #[("table", tableName), ("filter", filter), ("returning", ← returning tree command returned)]
    items command.start command.stop

end Belay.Sqlite.Translation
