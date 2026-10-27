import Belay.Sqlite.Translation.Conflicts

set_option doc.verso true

/-! Transaction control, INSERT, UPDATE and DELETE. The port of
{lit}`belay/sqlite/syntax_writes.py`: each write keeps its RETURNING columns and the subqueries
of its values, assignments and filter. Ordinary WITH prefixes retain definition templates
in the same query list; a subquery in RETURNING or ON CONFLICT is refused. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- The refusal of a subquery in RETURNING or ON CONFLICT. -/
def inWriteClause : String := "A subquery in RETURNING or ON CONFLICT is not modeled; read the value in a separate statement"

/-- {lit}`BEGIN [DEFERRED] [TRANSACTION]`, {lit}`COMMIT` or {lit}`END [TRANSACTION]`, and
{lit}`ROLLBACK [TRANSACTION]`. -/
def transaction (tree : SqlTree) (command : ParseNode) : TranslateM (Located Syntax.Statement) := do
  let keyword := (tree.children command)[0]!.symbol
  let option ← if keyword == "BEGIN" then do
      let parts ← require tree command ["BEGIN", "transtype", "trans_opt"]
      unless tree.symbols parts[1]! == [] || tree.symbols parts[1]! == ["DEFERRED"] do
        unsupported parts[1]! "Only deferred transactions are modeled; write BEGIN or BEGIN DEFERRED"
      pure parts[2]!
    else pure (← require tree command [keyword, "trans_opt"])[1]!
  unless tree.symbols option == [] || tree.symbols option == ["TRANSACTION"] do
    unsupported option "Named transactions are not modeled; remove the transaction name"
  let statement : Syntax.Statement := match keyword with | "BEGIN" => .begin | "ROLLBACK" => .rollback | _ => .commit
  return leaf statement command.start command.stop

/-- Whether the {lit}`select` node of an INSERT is a {lit}`VALUES` list, alone, and not a query: the form
that {lit}`valueRows` reads. -/
def isValuesSource (tree : SqlTree) (node : ParseNode) : Bool :=
  tree.symbols node == ["selectnowith"] &&
    tree.symbols (tree.children node)[0]! == ["oneselect"] &&
    [["values"], ["mvalues"]].contains (tree.symbols (tree.children (tree.children node)[0]!)[0]!)

/-- The VALUES rows of an INSERT source in text order; a trigger body refuses a query source here, and the
INSERT statement of a query is {lit}`insertQuery`. -/
def valueRows (tree : SqlTree) (node : ParseNode) : TranslateM (Located (List (List Syntax.Expr))) := do
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
def returning (tree : SqlTree) (command : ParseNode) (parts : Array ParseNode) :
    TranslateM (Located (List Syntax.ResultColumn)) := do
  if parts.isEmpty then return sequence #[] command.stop command.stop
  noSubqueries inWriteClause (resultColumns queryMappers tree parts[1]!)

/-- The column list of an {lit}`idlist_opt` node, or none. -/
def columnList (tree : SqlTree) (columns : ParseNode) : TranslateM (Located (Option (List Identifier))) := do
  if columns.children.isEmpty then return missing columns.start columns.stop
  let listed := (← require tree columns ["LP", "idlist", "RP"])[1]!
  let items ← leftList tree listed [(1, ["nm"]), (3, ["idlist", "COMMA", "nm"])]
  return (sequence (← items.mapM fun item => identifierName tree (last item)) columns.start columns.stop).present

/-- The subqueries of a statement, at the statement's range. -/
def subqueryList (items : Array (Located Syntax.Subquery)) (command : ParseNode) : Located (List Syntax.Subquery) :=
  sequence items command.start command.stop

/-- {lit}`INSERT [OR algorithm] INTO table [(columns)] SELECT ... [ON CONFLICT ...] [RETURNING columns]`, and
{lit}`REPLACE INTO`, with an optional ordinary WITH prefix (ADR 0017, S6; ADR 0019, D4). The query
is read as a {lit}`SELECT` statement is, with the definitions of the WITH prefix and its nested queries
in the subqueries of the source. Which text SQLite's grammar accepts is the parser's decision. -/
def insertQuery (tree : SqlTree) (command : ParseNode) (parts : Array ParseNode) :
    TranslateM (Located Syntax.Statement) := do
  let algorithm ← insertAlgorithm tree parts[1]!
  let (conflicts, returned) ← noSubqueries inWriteClause (conflictClauses tree parts[6]!)
  let table := (← require tree parts[3]! ["nm"])[0]!
  let columns ← columnList tree parts[4]!
  let (clauses, items) ← statementSubqueries do
    withDefinitions queryMappers tree parts[0]!
    queryClauses tree parts[5]!
  let tableName ← identifierName tree table
  let results ← returning tree command returned
  let subqueries := subqueryList items parts[5]!
  let source : Located Syntax.SelectBody := composite
    { columns := clauses.columns.value, source := clauses.source.value, joins := clauses.joins.value,
      filter := clauses.filter.value, groupBy := clauses.groupBy.value, orderBy := clauses.orderBy.value,
      limit := clauses.limit.value, offset := clauses.offset.value, subqueries := subqueries.value,
      having := clauses.having.value, distinct := clauses.distinct.value, compound := clauses.compound.value }
    parts[5]!.start parts[5]!.stop (clauses.selectSpans subqueries)
  return composite (.insertSelect tableName.value columns.value source.value conflicts.value algorithm.value
      results.value) command.start command.stop
    #[tableName.span, columns.span, source.span, conflicts.span, algorithm.span, results.span]

/-- {lit}`INSERT [OR algorithm] INTO table [(columns)] VALUES rows [ON CONFLICT ...] [RETURNING columns]`,
and {lit}`REPLACE INTO`, with an optional ordinary WITH prefix; the INSERT of a query is
{lit}`insertQuery`. -/
def insert (tree : SqlTree) (command : ParseNode) : TranslateM (Located Syntax.Statement) := do
  let parts ← require tree command ["with", "insert_cmd", "INTO", "xfullname", "idlist_opt", "select", "upsert"]
  if !isValuesSource tree parts[5]! then return ← insertQuery tree command parts
  let algorithm ← insertAlgorithm tree parts[1]!
  let (conflicts, returned) ← noSubqueries inWriteClause (conflictClauses tree parts[6]!)
  let table := (← require tree parts[3]! ["nm"])[0]!
  let columns ← columnList tree parts[4]!
  let (rows, items) ← statementSubqueries do
    withDefinitions queryMappers tree parts[0]!
    valueRows tree parts[5]!
  let tableName ← identifierName tree table
  let results ← returning tree command returned
  let subqueries := subqueryList items command
  return composite (.insert tableName.value columns.value rows.value conflicts.value algorithm.value results.value
      subqueries.value) command.start command.stop
    #[tableName.span, columns.span, rows.span, conflicts.span, algorithm.span, results.span, subqueries.span]

/-- The optional WHERE filter and the {lit}`RETURNING selcollist` parts of a
{lit}`where_opt_ret` node, which UPDATE and DELETE share; a missing filter is absent at the node. -/
def filterAndReturning (tree : SqlTree) (whereNode : ParseNode) (statement : String) :
    TranslateM (Located (Option Syntax.Expr) × Array ParseNode) := do
  let parts := tree.children whereNode
  let symbols := tree.symbols whereNode
  unless [[], ["WHERE", "expr"], ["RETURNING", "selcollist"], ["WHERE", "expr", "RETURNING", "selcollist"]].contains symbols do
    unsupported whereNode s!"Unsupported {statement} clause; write [WHERE expression] [RETURNING columns]"
  let filter ← if symbols.take 1 == ["WHERE"] then Located.present <$> queryExpression tree parts[1]!
    else pure (missing whereNode.start whereNode.stop)
  let returned := if symbols.drop (symbols.length - 2) == ["RETURNING", "selcollist"] then
    parts.extract (parts.size - 2) parts.size else #[]
  return (filter, returned)

/-- {lit}`UPDATE table SET assignments [WHERE expression] [RETURNING columns]`,
with an optional ordinary WITH prefix. -/
def update (tree : SqlTree) (command : ParseNode) : TranslateM (Located Syntax.Statement) := do
  let parts ← require tree command ["with", "UPDATE", "orconf", "xfullname", "indexed_opt", "SET", "setlist", "from",
    "where_opt_ret"]
  absent parts[2]! "An OR conflict clause"
  absent parts[4]! "INDEXED BY"
  absent parts[7]! "UPDATE FROM"
  let table := (← require tree parts[3]! ["nm"])[0]!
  let ((mapped, filter, returned), items) ← statementSubqueries do
    withDefinitions queryMappers tree parts[0]!
    let mapped ← assignmentList tree parts[6]!
    let (filter, returned) ← filterAndReturning tree parts[8]! "UPDATE"
    return (mapped, filter, returned)
  let tableName ← identifierName tree table
  let results ← returning tree command returned
  let subqueries := subqueryList items command
  return composite (.update tableName.value mapped.value filter.value results.value subqueries.value) command.start
    command.stop #[tableName.span, mapped.span, filter.span, results.span, subqueries.span]

/-- {lit}`DELETE FROM table [WHERE expression] [RETURNING columns]`,
with an optional ordinary WITH prefix. -/
def delete (tree : SqlTree) (command : ParseNode) : TranslateM (Located Syntax.Statement) := do
  let parts ← require tree command ["with", "DELETE", "FROM", "xfullname", "indexed_opt", "where_opt_ret"]
  absent parts[4]! "INDEXED BY"
  let table := (← require tree parts[3]! ["nm"])[0]!
  let ((filter, returned), items) ← statementSubqueries do
    withDefinitions queryMappers tree parts[0]!
    filterAndReturning tree parts[5]! "DELETE"
  let tableName ← identifierName tree table
  let results ← returning tree command returned
  let subqueries := subqueryList items command
  return composite (.delete tableName.value filter.value results.value subqueries.value) command.start command.stop
    #[tableName.span, filter.span, results.span, subqueries.span]

end Belay.Sqlite.Translation
