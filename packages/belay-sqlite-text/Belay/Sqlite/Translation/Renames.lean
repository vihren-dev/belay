import Belay.Sqlite.Translation.Expressions

set_option doc.verso true

/-! ALTER TABLE RENAME TO and ALTER TABLE RENAME COLUMN. Each production maps to one constructor without
reading the schema; a schema name before the table is refused with its range. The old column name is kept
as written ({lit}`columnToken`) because SQLite prints it with its quotes in the error of a missing column,
and the new name keeps whether it was written with a quote, because that decides how SQLite writes the new
column name in the stored text of the objects that use it. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- The table name of an unqualified {lit}`fullname`. -/
def alterTableName (tree : SqlTree) (full : ParseNode) : TranslateM (Located Identifier) := do
  identifierName tree (← require tree full ["nm"])[0]!

/-- Whether a name token is written with a quote of any of the four kinds. -/
def writtenWithQuote (tree : SqlTree) (node : ParseNode) : TranslateM Bool := do
  let item ← if node.children.isEmpty then pure node else token tree node
  return ['"', '\'', '`', '['].contains ((tree.text item).toList.headD ' ')

/-- {lit}`ALTER TABLE t RENAME TO u` for an unqualified table name. -/
def renameTable (tree : SqlTree) (command : ParseNode) : TranslateM (Located Syntax.Statement) := do
  let parts ← require tree command ["ALTER", "TABLE", "fullname", "RENAME", "TO", "nm"]
  let table ← alterTableName tree parts[2]!
  let newName ← identifierName tree parts[5]!
  return composite (.renameTable table.value newName.value) command.start command.stop #[table.span, newName.span]

/-- {lit}`ALTER TABLE t RENAME [COLUMN] a TO b` for an unqualified table name. -/
def renameColumn (tree : SqlTree) (command : ParseNode) : TranslateM (Located Syntax.Statement) := do
  let parts ← require tree command ["ALTER", "TABLE", "fullname", "RENAME", "kwcolumn_opt", "nm", "TO", "nm"]
  let table ← alterTableName tree parts[2]!
  let column ← identifierName tree parts[5]!
  let newName ← identifierName tree parts[7]!
  let columnToken := tree.text (← token tree parts[5]!)
  let quoted ← writtenWithQuote tree parts[7]!
  return composite (.renameColumn table.value column.value newName.value columnToken quoted) command.start
    command.stop #[table.span, column.span, newName.span]

end Belay.Sqlite.Translation
