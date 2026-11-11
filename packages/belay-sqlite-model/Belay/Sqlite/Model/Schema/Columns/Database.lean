import Belay.Sqlite.Model.Schema.Ddl.CatalogDrop
import Belay.Sqlite.Model.Schema.ForeignKeys.ParentKeys
import Belay.Sqlite.Model.Values.Scalar.StoreValue
import Belay.Sqlite.Model.Shared.Catalog.Database

set_option doc.verso true

/-! The database: a catalog and the stored rows of each catalog object. No coercions,
SQL expressions or native-engine correctness are assumed here. The catalog is the only
record of the schema; {lit}`Database.table` pairs a table's catalog entry with its rows.
The facts of an admitted and of a valid database are in {lit}`DatabaseFacts` and
{lit}`DatabaseConstraints`. -/

namespace Belay.Sqlite.Model

/-- Append each column and its supplied value to every row of the table view. Apply each
new column's affinity to its value; preserve existing cells, rowids, row order and keys.
Supply {lean}`Value.null` for a column without a default. An empty list leaves the table
unchanged. {lit}`Database.addColumn` does this to a stored table. -/
def Table.appendColumns (table : Table) (columns : List (CatalogColumn × Value)) : Table :=
  { table with
    shape.columns := table.shape.columns ++ columns.map Prod.fst
    rows := table.rows.map (·.appendValues (columns.map fun (column, value) => Value.store column.affinity value)) }

/-- ADD COLUMN in the database: append the column to the table at the position
({name}`Catalog.addColumn`) and the value, with the column's affinity applied, to each of
its rows. Rowids, row order, the other cells and every other position are unchanged.
Supply {lean}`Value.null` for a column without a default. -/
def Database.addColumn (database : Database) (position : Nat) (column : CatalogColumn) (value : Value) :
    Database :=
  { catalog := database.catalog.addColumn position column,
    rows := database.rows.modify position (·.map (·.appendValues [Value.store column.affinity value])) }

end Belay.Sqlite.Model
