import Belay.Sqlite.Translation.Columns

set_option doc.verso true

/-! CREATE TABLE and ALTER TABLE ADD COLUMN. The port of the table part of
{lit}`belay/sqlite/syntax_definitions.py`: each production maps to one constructor without
reading the schema; TEMP, IF NOT EXISTS and a schema name are refused with their range. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- A key column list of plain names, without sort order, collation or expressions. -/
def sortNames (tree : SqlTree) (node : ParseNode) : TranslateM (Located (List Identifier)) := do
  let items ← leftList tree node [(3, ["expr", "sortorder", "nulls"]), (5, ["sortlist", "COMMA", "expr", "sortorder", "nulls"])]
  let names ← items.mapM fun item => do
    absent (fromEnd item 2) "A sort order in a key"
    absent (last item) "NULLS FIRST or NULLS LAST"
    identifierName tree (← require tree (fromEnd item 3) ["ID"])[0]!
  return sequence names node.start node.stop

/-- A table PRIMARY KEY or UNIQUE constraint over plain column names, with its ON CONFLICT
algorithm, a CHECK with the label of the constraint name in effect, and a FOREIGN KEY. -/
def tableConstraint (tree : SqlTree) (node : ParseNode) (current : Option String) :
    TranslateM (Located Syntax.TableConstraint) := do
  let parts := tree.children node
  match tree.symbols node with
  | ["CHECK", "LP", "expr", "RP", "onconf"] => check tree node parts current (.check · · ·)
  | ["FOREIGN", "KEY", "LP", "eidlist", "RP", "REFERENCES", "nm", "eidlist_opt", "refargs", "defer_subclause_opt"] =>
    foreignKey tree node parts
  | ["PRIMARY", "KEY", "LP", "sortlist", "autoinc", "RP", "onconf"] =>
    absent parts[4]! "AUTOINCREMENT"
    let columns ← sortNames tree parts[3]!
    let algorithm ← constraintAlgorithm tree parts[6]!
    return composite (.primaryKey columns.value algorithm.value) node.start node.stop #[columns.span, algorithm.span]
  | ["UNIQUE", "LP", "sortlist", "RP", "onconf"] =>
    let columns ← sortNames tree parts[2]!
    let algorithm ← constraintAlgorithm tree parts[4]!
    return composite (.unique columns.value algorithm.value) node.start node.stop #[columns.span, algorithm.span]
  | _ => unsupported node ("Unsupported table constraint; use PRIMARY KEY or UNIQUE over column names, " ++
      "CHECK or FOREIGN KEY")

/-- The table options {lit}`WITHOUT ROWID` and {lit}`STRICT`, each word in either ASCII case;
{lit}`strict` is present only when true. -/
def tableOptions (tree : SqlTree) (node : ParseNode) : TranslateM (Located Syntax.TableOptions) := do
  let mut withoutRowid := false
  let mut strict := false
  for item in ← leftList tree node [(1, ["table_option"]), (3, ["table_option_set", "COMMA", "table_option"])] do
    let option := last item
    let parts := tree.children option
    match tree.symbols option with
    | ["WITHOUT", "nm"] =>
      if asciiEqual (tree.text parts[1]!) "rowid" then withoutRowid := true
      else unsupported option "Unknown table option; use WITHOUT ROWID or STRICT"
    | ["nm"] =>
      if asciiEqual (tree.text parts[0]!) "strict" then strict := true
      else unsupported option "Unknown table option; use WITHOUT ROWID or STRICT"
    | _ => unsupported option "Unknown table option; use WITHOUT ROWID or STRICT"
  let parts := if strict then #[spanOf node, spanOf node] else #[spanOf node]
  return composite { withoutRowid, strict } node.start node.stop parts

/-- The table constraints of a {lit}`conslist`, with the constraint name in effect from the last
column until a comma between table constraints; the deferral clause of a FOREIGN KEY is a
{lit}`deferral` constraint after it. -/
def tableConstraints (tree : SqlTree) (listed : ParseNode) (last' : Option String) :
    TranslateM (Array (Located Syntax.TableConstraint)) := do
  let mut constraints : Array (Located Syntax.TableConstraint) := #[]
  let mut current := last'
  for item in ← leftList tree listed [(1, ["tcons"]), (3, ["conslist", "tconscomma", "tcons"])] do
    if item.size == 2 && !item[0]!.children.isEmpty then current := none
    let constraint := last item
    let parts := tree.children constraint
    if tree.symbols constraint == ["CONSTRAINT", "nm"] then
      current := some (constraintName tree parts[1]!)
    else
      constraints := constraints.push (← tableConstraint tree constraint current)
      let final := parts.back!
      if final.symbol == "defer_subclause_opt" && !final.children.isEmpty then
        constraints := constraints.push (deferral tree (tree.children final)[0]! .deferral)
  return constraints

/-- CREATE TABLE with column definitions and table constraints. -/
def createTable (tree : SqlTree) (command : ParseNode) : TranslateM (Located Syntax.Statement) := do
  let parts := tree.children command
  let header ← require tree parts[0]! ["createkw", "temp", "TABLE", "ifnotexists", "nm", "dbnm"]
  let body ← require tree parts[1]! ["LP", "columnlist", "conslist_opt", "RP", "table_option_set"]
  absent header[1]! "TEMP"
  absent header[3]! "IF NOT EXISTS"
  absent header[5]! "A schema name"
  let mut columns : Array (Located Syntax.ColumnDefinition) := #[]
  let mut current : Option String := none
  for item in ← leftList tree body[1]! [(2, ["columnname", "carglist"]), (4, ["columnlist", "COMMA", "columnname", "carglist"])] do
    let (definition, named) ← columnDefinition tree (fromEnd item 2) (last item)
    columns := columns.push definition
    current := named
  let constraints ← if body[2]!.children.isEmpty then pure #[] else
    tableConstraints tree (← require tree body[2]! ["COMMA", "conslist"])[1]! current
  let tableName ← identifierName tree header[4]!
  let columnList := sequence columns body[1]!.start body[1]!.stop
  let constraintList := sequence constraints body[2]!.start body[2]!.stop
  let options ← tableOptions tree body[4]!
  return composite (.createTable tableName.value columnList.value constraintList.value options.value) command.start
    command.stop #[tableName.span, columnList.span, constraintList.span, options.span]

/-- {lit}`ALTER TABLE ADD [COLUMN]` for an unqualified table name. -/
def addColumn (tree : SqlTree) (command : ParseNode) : TranslateM (Located Syntax.Statement) := do
  let parts ← require tree command ["ALTER", "TABLE", "add_column_fullname", "ADD", "kwcolumn_opt", "columnname", "carglist"]
  let full := (← require tree parts[2]! ["fullname"])[0]!
  let table := (← require tree full ["nm"])[0]!
  let tableName ← identifierName tree table
  let (column, _) ← columnDefinition tree parts[5]! parts[6]!
  return composite (.addColumn tableName.value column.value) command.start command.stop #[tableName.span, column.span]

end Belay.Sqlite.Translation
