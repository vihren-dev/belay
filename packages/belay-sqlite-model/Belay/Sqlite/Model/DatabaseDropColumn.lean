import Belay.Sqlite.Model.Database
import Belay.Sqlite.Model.Resolution.ColumnDropCatalog
import Belay.Sqlite.Model.Resolution.CatalogOutline

set_option doc.verso true

/-! The rows and the database after ALTER TABLE DROP COLUMN (ADR 0019, D4): the cell of the dropped column
leaves every row of its table. Rowids, row order, the other cells in their order and every other table stay.
{lit}`Database.dropColumn` is what {lit}`step` stores for a dropped column. -/

namespace Belay.Sqlite.Model

/-- The row without the cell at the index. The rowid stays. A row that has no cell at the index stays
as it is. -/
def Row.dropValue (index : Nat) (row : Row) : Row :=
  { row with values := row.values.eraseIdx index }

/-- DROP COLUMN in the database: store the catalog of the statement, and remove the cell at the index
from each row of the table at the position ({name}`Row.dropValue`). Rowids, row order, the other cells and every
other position are unchanged. -/
def Database.dropColumn (database : Database) (position index : Nat) (stored : Catalog) : Database :=
  { catalog := stored, rows := database.rows.modify position (·.map (Row.dropValue index)) }

/-- Whether the model runs a DROP COLUMN statement on the database: the column can leave the table
({name}`Catalog.droppable`), and the catalog of the statement has the outline of the catalog without the column
and the selected parents of it ({name}`Catalog.keepsOutline`), so that a view or a trigger may change its
definition and nothing else may differ. When it does not, {lit}`step` fails as {lit}`ExecutionError.unmodeled`
and keeps the database. -/
def Database.runsDropColumn (database : Database) (position index : Nat) (stored : Catalog) : Bool :=
  database.catalog.droppable position index && (database.catalog.dropColumn position index).keepsOutline stored

end Belay.Sqlite.Model
