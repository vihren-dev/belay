import Belay.Sqlite.Model.Resolution.ColumnDropKeys
import Belay.Sqlite.Model.Resolution.CatalogObjects

set_option doc.verso true

/-! The catalog table after ALTER TABLE DROP COLUMN (ADR 0019, D4): the column is gone, with its own
CHECK constraints, generated expression and column-level foreign keys, and every position that the table
keeps moves as {lit}`dropPosition` says. The table keeps the order of its other columns and the
algorithms of its keys. -/

namespace Belay.Sqlite.Model

/-- The name token of a CHECK text with its target changed for the drop of the column at {lit}`index`. -/
def LabelName.dropColumn (index : Nat) (name : LabelName) : LabelName :=
  match name.target with
  | .table => name
  | .column position => { name with target := .column (dropPosition index position) }

/-- The CHECK constraint with its condition and the targets of the tokens of its text changed for the
drop of the column at {lit}`index`. -/
def CheckConstraint.dropColumn (index : Nat) (check : CheckConstraint) : CheckConstraint :=
  { check with condition := check.condition.dropColumn index,
               source := check.source.map fun text => { text with names := text.names.map (·.dropColumn index) } }

/-- The foreign key with the positions of its child columns changed for the drop of the column at
{lit}`index`. -/
def ForeignKey.dropColumn (index : Nat) (key : ForeignKey) : ForeignKey :=
  { key with columns := key.columns.map (dropPosition index) }

/-- The column with the positions in its CHECK constraints, generated expression and foreign keys changed
for the drop of the column at {lit}`index`. -/
def CatalogColumn.dropColumn (index : Nat) (column : CatalogColumn) : CatalogColumn :=
  { column with checks := column.checks.map (·.dropColumn index),
                foreignKeys := column.foreignKeys.map (·.dropColumn index),
                generated := column.generated.map fun how => { how with expression := how.expression.dropColumn index } }

/-- The table without the column at {lit}`index`, with every position that the table keeps changed
({lit}`dropPosition`): the other columns, the primary key, the rowid alias, the UNIQUE keys, the CHECK
constraints and the foreign keys of the table constraints. -/
def CatalogTable.dropColumnAt (index : Nat) (table : CatalogTable) : CatalogTable :=
  { table with
    columns := (table.columns.eraseIdx index).map (·.dropColumn index)
    primaryKey := table.primaryKey.map (dropPosition index)
    rowidAlias := table.rowidAlias.map (dropPosition index)
    uniqueKeys := table.uniqueKeys.map (·.map (dropPosition index))
    checks := table.checks.map (·.dropColumn index)
    foreignKeys := table.foreignKeys.map (·.dropColumn index)
    inlineUnique := table.inlineUnique.map (dropPosition index) }

end Belay.Sqlite.Model
