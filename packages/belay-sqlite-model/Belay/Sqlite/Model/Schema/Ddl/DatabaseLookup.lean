import Belay.Sqlite.Model.Schema.Columns.Database
import Belay.Sqlite.Model.Schema.Ddl.CatalogSpec

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

/-- For every two databases with the same catalog and every position that has a table in that catalog: the first
database has at the position the table of the catalog entry with the rows that it stores at the position, or no
rows when its row store has no entry at the position. A proof that knows the second database, for example a fixed
schema, computes the entry there. Proof sketch: {name}`Database.table` maps the entry of the catalog. -/
theorem Database.table_of_sameCatalog {database schema : Database} (same : database.catalog = schema.catalog)
    (position : Nat) (present : (schema.catalog.tableAt position).isSome = true) :
    database.table position =
      some { shape := (schema.catalog.tableAt position).get present, rows := database.rows.getD position [] } := by
  unfold Database.table
  rw [same]
  conv => lhs; rw [← Option.some_get present]
  rfl

end Belay.Sqlite.Model
