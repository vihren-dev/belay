import Belay.Sqlite.Model.Database
import Belay.Sqlite.Model.Resolution.CatalogSpec

set_option doc.verso true

/-! The agreement between catalog lookups and database tables. These facts connect
a table's schema to its stored rows without requiring an admitted database. -/

namespace Belay.Sqlite.Model

/-- For every database, name, position and catalog table that the lookup of the catalog finds, the
database has the table at that position: the catalog table with the stored rows of the position.
Proof sketch: {name}`Catalog.findTable_some` gives the object of the catalog at the position, which
is a table; unfold {name}`Database.table` and {name}`Catalog.tableAt`. -/
theorem Database.table_of_findTable (database : Database) (name : Identifier) (position : Nat) (shape : CatalogTable)
    (found : database.catalog.findTable name = some (position, shape)) :
    database.table position = some { shape, rows := database.rows.getD position [] } := by
  obtain ⟨⟨objectName, objectEntry⟩, atPosition, entry, -⟩ := Catalog.findTable_some _ _ _ _ found
  cases entry
  simp [Database.table, Catalog.tableAt, atPosition]

end Belay.Sqlite.Model
