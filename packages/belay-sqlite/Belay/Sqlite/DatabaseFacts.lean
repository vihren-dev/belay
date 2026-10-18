import Belay.Sqlite.Model

set_option doc.verso true

/-! How the database operations change the table view {name}`Belay.Sqlite.Database.table`.
Proofs about execution use these lemmas instead of unfolding the catalog and row lists. -/

namespace Belay.Sqlite
/-- For every row list and index, appending one empty row list does not change the rows
that {lit}`getD` gives with the empty default. -/
theorem rows_getD_append_nil : ∀ (rows : List (List Row)) (index : Nat),
    (rows ++ [[]]).getD index [] = rows.getD index []
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: rest, index + 1 => rows_getD_append_nil rest index

/-- For every catalog and position that holds a table, {name}`Catalog.createTable` keeps
the table at that position. -/
theorem Catalog.tableAt_createTable {catalog : Catalog} {position : Nat} {shape : CatalogTable}
    (name : String) (table : CatalogTable) (present : catalog.tableAt position = some shape) :
    (catalog.createTable name table).tableAt position = some shape := by
  have below : position < catalog.length := by
    unfold Catalog.tableAt at present
    cases h : catalog[position]? with
    | none => simp [h] at present
    | some _ => exact (List.getElem?_eq_some_iff.mp h).1
  unfold Catalog.tableAt at present ⊢
  simpa [Catalog.createTable, List.getElem?_append_left below] using present

/-- For every database, name, table and position with a table in the view, the database
after CREATE TABLE ({name}`Catalog.createTable` with an empty row list appended) has the
same table at that position. -/
theorem Database.table_createTable {database : Database} {position : Nat} {table : Table}
    (name : String) (shape : CatalogTable) (present : database.table position = some table) :
    ({ catalog := database.catalog.createTable name shape, rows := database.rows ++ [[]] } : Database).table
      position = some table := by
  unfold Database.table at present ⊢
  cases h : database.catalog.tableAt position with
  | none => simp [h] at present
  | some old =>
    simp only [h, Option.map_some, Option.some.injEq] at present
    subst present
    simp only [Catalog.tableAt_createTable name shape h, Option.map_some, rows_getD_append_nil]

/-- For every catalog, position that holds a table and column, after
{name}`Catalog.addColumn` the position holds the table with the column appended. -/
theorem Catalog.tableAt_addColumn_same {catalog : Catalog} {position : Nat} {shape : CatalogTable}
    (column : CatalogColumn) (present : catalog.tableAt position = some shape) :
    (catalog.addColumn position column).tableAt position = some { shape with columns := shape.columns ++ [column] } := by
  unfold Catalog.tableAt at present
  unfold Catalog.addColumn
  split at present
  · rename_i name found
    have below : position < catalog.length := (List.getElem?_eq_some_iff.mp found).1
    simp only [found, Option.some.injEq] at present ⊢
    subst present
    simp [Catalog.tableAt, List.getElem?_set_self below]
  · simp at present
  · simp at present

/-- For every catalog, two distinct positions and column, {name}`Catalog.addColumn` at one
position leaves the entry at the other position unchanged. -/
theorem Catalog.tableAt_addColumn_other (catalog : Catalog) {position other : Nat} (column : CatalogColumn)
    (distinct : other ≠ position) : (catalog.addColumn position column).tableAt other = catalog.tableAt other := by
  unfold Catalog.addColumn
  split
  · simp [Catalog.tableAt, List.getElem?_set_ne (Ne.symm distinct)]
  · rfl
  · rfl

/-- For every database, position, column and value: if the view has a table at the
position, then after {name}`Database.addColumn` the view has that table with the column
appended ({name}`Table.appendColumns`). -/
theorem Database.table_addColumn {database : Database} {position : Nat} {table : Table}
    (column : CatalogColumn) (value : Value) (present : database.table position = some table) :
    (database.addColumn position column value).table position = some (table.appendColumns [(column, value)]) := by
  unfold Database.table at present ⊢
  cases h : database.catalog.tableAt position with
  | none => simp [h] at present
  | some old =>
    simp only [h, Option.map_some, Option.some.injEq] at present
    subst present
    simp only [Database.addColumn, Catalog.tableAt_addColumn_same column h, Option.map_some, Option.some.injEq,
      Table.appendColumns, List.getD_eq_getElem?_getD, List.getElem?_modify]
    cases database.rows[position]? <;> simp

/-- For every database, two distinct positions, column and value,
{name}`Database.addColumn` at one position leaves the view at the other position unchanged. -/
theorem Database.table_addColumn_other (database : Database) {position other : Nat} (column : CatalogColumn)
    (value : Value) (distinct : other ≠ position) :
    (database.addColumn position column value).table other = database.table other := by
  simp [Database.table, Database.addColumn, Catalog.tableAt_addColumn_other _ column distinct,
    List.getD_eq_getElem?_getD, Ne.symm distinct]

/-- For every database, position below the length of its row lists, table and rows: if
the view has the table at the position, then after {name}`Database.setRows` it has the
table with the rows. -/
theorem Database.table_setRows {database : Database} {position : Nat} {table : Table} (rows : List Row)
    (present : database.table position = some table) (aligned : position < database.rows.length) :
    (database.setRows position rows).table position = some { table with rows } := by
  unfold Database.table at present ⊢
  cases h : database.catalog.tableAt position with
  | none => simp [h] at present
  | some old =>
    simp only [h, Option.map_some, Option.some.injEq] at present
    subst present
    simp [Database.setRows, h, List.getD_eq_getElem?_getD, List.getElem?_set_self aligned]

/-- For every database, two distinct positions and rows, {name}`Database.setRows` at one
position leaves the view at the other position unchanged. -/
theorem Database.table_setRows_other (database : Database) {position other : Nat} (rows : List Row)
    (distinct : other ≠ position) : (database.setRows position rows).table other = database.table other := by
  simp [Database.table, Database.setRows, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm distinct)]
/-- For every catalog, position below its length, column, name and table, ADD COLUMN at
the position and CREATE TABLE commute: either order gives the same catalog. -/
theorem Catalog.addColumn_createTable (catalog : Catalog) {position : Nat} (column : CatalogColumn) (name : String)
    (table : CatalogTable) (below : position < catalog.length) :
    (catalog.createTable name table).addColumn position column = (catalog.addColumn position column).createTable name table := by
  unfold Catalog.addColumn Catalog.createTable
  rw [List.getElem?_append_left below]
  split <;> rename_i found <;> simp [found, List.set_append_left _ _ below]

/-- For every database whose row lists match its catalog, position below the catalog
length, column, value, name and table, ADD COLUMN at the position and CREATE TABLE commute:
either order gives the same database. -/
theorem Database.addColumn_createTable (database : Database) {position : Nat} (column : CatalogColumn) (value : Value)
    (name : String) (table : CatalogTable) (below : position < database.catalog.length)
    (aligned : database.rows.length = database.catalog.length) :
    ({ catalog := database.catalog.createTable name table, rows := database.rows ++ [[]] } : Database).addColumn
        position column value =
      { catalog := (database.addColumn position column value).catalog.createTable name table,
        rows := (database.addColumn position column value).rows ++ [[]] } := by
  simp only [Database.addColumn, Database.mk.injEq]
  refine ⟨Catalog.addColumn_createTable _ column name table below, ?_⟩
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_modify, List.getElem?_append]
  split <;> split <;> simp_all <;> omega

end Belay.Sqlite
