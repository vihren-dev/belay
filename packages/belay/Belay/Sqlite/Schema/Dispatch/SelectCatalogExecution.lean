import Belay.Sqlite.Schema.Dispatch.ReadAnalysis
import Belay.Sqlite.Queries.Evaluation.SelectCatalogExecution
import Belay.Sqlite.Schema.Rows.Database

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- The rows of the table at a catalog position, each as its values in column order, in the order of a
full scan; no rows when the position has no table. For example, {lit}`db.scanAt 0` is the rows of the
first table of the catalog. -/
def Database.scanAt (db : Database) (position : Nat) : List (List Value) :=
  ((db.raw.table position).map Resolved.sourceRows).getD []

/-- For every database {lit}`db`, database {lit}`catalog` whose catalog {lit}`db` has, and catalog
position with the table {lit}`shape` in the catalog: {lit}`db` has at the position the table of
{lit}`shape` with its stored rows, and the scanned rows at the position ({name}`Database.scanAt`) are
the rows of that table ({name}`Resolved.sourceRows`). Proof sketch: the two databases have the same
catalog. -/
theorem Database.table_of_catalog {db catalog : Database} (schema : db.HasCatalog catalog) {position : Nat}
    {shape : CatalogTable} (present : catalog.raw.catalog.tableAt position = some shape) :
    db.raw.table position = some { shape, rows := db.raw.rows.getD position [] } ∧
      db.scanAt position = Resolved.sourceRows { shape, rows := db.raw.rows.getD position [] } := by
  have table : db.raw.table position = some { shape, rows := db.raw.rows.getD position [] } := by
    simp [Database.table, show db.raw.catalog = catalog.raw.catalog from schema, present]
  exact ⟨table, by simp [Database.scanAt, table]⟩

/-- Source rule of a scan: for every database {lit}`db`, database {lit}`catalog` whose catalog
{lit}`db` has, catalog position with the table {lit}`shape` in the catalog, and scanned row of
{lit}`db` at the position ({name}`Database.scanAt`), the row has one cell for each column of
{lit}`shape`, and no cell of a NOT NULL column is NULL ({name}`NotNullCells`). Proof sketch: the
scanned row is the values of a stored row, which the validity of {lit}`db` makes as wide as the table
and keeps from NULL in a NOT NULL column. -/
theorem Database.mem_scanAt {db catalog : Database} (schema : db.HasCatalog catalog) {position : Nat}
    {shape : CatalogTable} (present : catalog.raw.catalog.tableAt position = some shape) {row : List Value}
    (member : row ∈ db.scanAt position) :
    row.length = shape.columns.length ∧ NotNullCells (shape.columns.map (·.notNull)) row := by
  have table : db.raw.table position = some { shape, rows := db.raw.rows.getD position [] } := by
    simp [Database.table, show db.raw.catalog = catalog.raw.catalog from schema, present]
  simp only [Database.scanAt, table, Option.map_some, Option.getD_some] at member
  obtain ⟨stored, storedIn, rfl⟩ := (mem_sourceRows_iff _ _).mp member
  have wide := db.valid.admitted.rowsWide position _ table stored storedIn
  refine ⟨wide, ?_⟩
  have cells : ∀ (index : Nat) (column : CatalogColumn) (value : Value), shape.columns[index]? = some column →
      stored.values[index]? = some value → column.notNull = true → value ≠ .null := fun index column value =>
    db.notNull position _ table stored storedIn index column value
  clear wide storedIn table
  generalize stored.values = values at cells
  generalize shape.columns = columns at cells
  induction columns generalizing values with
  | nil => simp [NotNullCells]
  | cons column columns step =>
    cases values with
    | nil => cases column.notNull <;> simp [NotNullCells]
    | cons value values =>
      have rest := step values fun index => cells (index + 1)
      cases required : column.notNull
      · simpa [NotNullCells, required] using rest
      · simpa [NotNullCells, required] using And.intro (cells 0 column value rfl rfl required) rest

end Belay.Sqlite
