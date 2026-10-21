import Belay.Sqlite.Model.ModelLaws
import Belay.Sqlite.Model.StoreValueLaws
import Belay.Sqlite.Model.DatabaseLaws

set_option doc.verso true

/-! Catalog updates for added columns keep lookup proofs independent of the catalog
size. -/
namespace Belay.Sqlite.Model

/-- For every valid table and list of column/value pairs, {name}`Table.appendColumns`
remains valid. With no rows, rowid and width conditions are vacuous. Column
support is a separate catalog check. The proof preserves old cells and rowids,
adds equal numbers of columns and cells, and uses idempotence of
{name}`storeValue` for the appended cells. -/
theorem Table.Valid.appendColumns {table : Table} {columns : List (CatalogColumn × Value)} (valid : table.Valid) :
    (table.appendColumns columns).Valid := by
  refine ⟨?_, ?_⟩
  · simpa [Table.appendColumns, Row.appendValues, List.map_map, Function.comp_def] using valid.1
  · intro row member
    obtain ⟨original, oldMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨rowid, width, stored, aliased⟩ := valid.2 original oldMember
    refine ⟨rowid, by simp [Row.appendValues, Table.appendColumns, width], ?_, ?_⟩
    rotate_left
    · intro position alias
      have cell := aliased position alias
      have old : position < original.values.length := (List.getElem?_eq_some_iff.mp cell).1
      simpa [Table.appendColumns, Row.appendValues, List.getElem?_append_left old] using cell
    intro position column value columnAt cellAt
    simp only [Table.appendColumns, Row.appendValues] at columnAt cellAt
    by_cases old : position < original.values.length
    · rw [List.getElem?_append_left old] at cellAt
      rw [List.getElem?_append_left (width ▸ old)] at columnAt
      exact stored position column value columnAt cellAt
    · rw [List.getElem?_append_right (by omega)] at cellAt
      rw [List.getElem?_append_right (by omega)] at columnAt
      rw [← width] at columnAt
      cases found : columns[position - original.values.length]? with
      | none => simp [List.getElem?_map, found] at cellAt
      | some pair =>
        simp [List.getElem?_map, found] at columnAt cellAt
        subst column
        subst value
        exact storeValue_storeValue _ _

/-- For every catalog, position and column, {name}`Catalog.addColumn` keeps the number of
catalog objects. -/
theorem Catalog.length_addColumn (catalog : Catalog) (position : Nat) (column : CatalogColumn) :
    (catalog.addColumn position column).length = catalog.length := by
  unfold Catalog.addColumn
  split <;> simp

/-- For every profile, catalog, database, table, position, column and value, assume:
* The original database satisfies {name}`Conforms` with the original catalog.
* The view has the given table at the selected position.
* The catalog from {name}`Catalog.addColumn` satisfies {name}`Catalog.Valid`.
Then {name}`Database.addColumn` satisfies {name}`Conforms` with the extended catalog. A
position without a table cannot satisfy the second assumption. Use this theorem after
checking the new catalog. Proof sketch: the changed table is the old valid table with the
column appended ({name}`Database.table_addColumn`, {name}`Table.Valid.appendColumns`);
every other position is unchanged ({name}`Database.table_addColumn_other`). -/
theorem Conforms.addColumn {catalog : Catalog} {database : Database} {table : Table} {column : CatalogColumn}
    (value : Value) (conforms : Conforms profile catalog database) (present : database.table position = some table)
    (catalogValid : (catalog.addColumn position column).Valid profile.limits) :
    Conforms profile (catalog.addColumn position column) (database.addColumn position column value) := by
  obtain ⟨same, _, length, each⟩ := conforms
  subst same
  refine ⟨rfl, catalogValid, by simp [Database.addColumn, Catalog.length_addColumn, length], fun other => ⟨?_, ?_⟩⟩
  · intro absent
    by_cases equal : other = position
    · subst other
      have kept := Database.table_addColumn column value present
      simp [Database.table, absent] at kept
    · have unchanged := (each other).1
      change (database.catalog.addColumn position column).tableAt other = none at absent
      rw [Catalog.tableAt_addColumn_other _ column equal] at absent
      simpa [Database.addColumn, List.getD_eq_getElem?_getD, List.getElem?_modify, Ne.symm equal] using
        unchanged absent
  · intro result found
    by_cases equal : other = position
    · subst other
      rw [Database.table_addColumn column value present] at found
      cases found
      exact ((each position).2 table present).appendColumns
    · rw [Database.table_addColumn_other database column value equal] at found
      exact (each other).2 result found
/-- For every catalog, name, table and position below the catalog length,
{name}`Catalog.createTable` keeps the entry at the position. -/
theorem Catalog.tableAt_createTable_below (catalog : Catalog) (name : Identifier) (table : CatalogTable)
    {position : Nat} (below : position < catalog.length) :
    (catalog.createTable name table).tableAt position = catalog.tableAt position := by
  simp [Catalog.tableAt, Catalog.createTable, List.getElem?_append_left below]

/-- For every catalog, name and table, after {name}`Catalog.createTable` the position
{lean}`catalog.length` holds the new table. -/
theorem Catalog.tableAt_createTable_end (catalog : Catalog) (name : Identifier) (table : CatalogTable) :
    (catalog.createTable name table).tableAt catalog.length = some table := by
  simp [Catalog.tableAt, Catalog.createTable]

/-- For every catalog, name, table and position above the catalog length, the position
holds no table after {name}`Catalog.createTable`. -/
theorem Catalog.tableAt_createTable_above (catalog : Catalog) (name : Identifier) (table : CatalogTable)
    {position : Nat} (above : catalog.length < position) :
    (catalog.createTable name table).tableAt position = none := by
  simp [Catalog.tableAt, Catalog.createTable, List.getElem?_eq_none (by simp; omega : (catalog ++ [_]).length ≤ position)]

/-- For every profile, catalog, database, name and table, assume:
* The database satisfies {name}`Conforms` with the catalog.
* The catalog from {name}`Catalog.createTable` satisfies {name}`Catalog.Valid`.
Then the database after CREATE TABLE (the new catalog, and an empty row list appended)
satisfies {name}`Conforms` with the new catalog. Proof sketch: positions below the old
length keep their entry and rows; the new position holds the table with no rows; positions
above it hold nothing. -/
theorem Conforms.createTable {catalog : Catalog} {database : Database} (name : Identifier) (table : CatalogTable)
    (conforms : Conforms profile catalog database)
    (catalogValid : (catalog.createTable name table).Valid profile.limits) :
    Conforms profile (catalog.createTable name table)
      { catalog := database.catalog.createTable name table, rows := database.rows ++ [[]] } := by
  obtain ⟨same, _, length, each⟩ := conforms
  subst same
  refine ⟨rfl, catalogValid, by simp [Catalog.createTable, length], fun position => ⟨?_, ?_⟩⟩
  · intro absent
    change (database.catalog.createTable name table).tableAt position = none at absent
    change (database.rows ++ [[]]).getD position [] = []
    rw [rows_getD_append_nil]
    rcases Nat.lt_trichotomy position database.catalog.length with below | equal | above
    · rw [Catalog.tableAt_createTable_below _ _ _ below] at absent
      exact (each position).1 absent
    · subst equal
      rw [Catalog.tableAt_createTable_end] at absent
      cases absent
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : database.rows.length ≤ position)]
  · intro result found
    rcases Nat.lt_trichotomy position database.catalog.length with below | equal | above
    · have kept : ({ catalog := database.catalog.createTable name table, rows := database.rows ++ [[]] } : Database).table
          position = database.table position := by
        simp only [Database.table, Catalog.tableAt_createTable_below _ _ _ below, rows_getD_append_nil]
      rw [kept] at found
      exact (each position).2 result found
    · subst equal
      simp only [Database.table, Catalog.tableAt_createTable_end, Option.map_some, Option.some.injEq,
        rows_getD_append_nil] at found
      subst found
      have empty : database.rows.getD database.catalog.length [] = [] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : database.rows.length ≤ database.catalog.length)]
      rw [empty]
      exact ⟨by simp, fun _ member => by simp at member⟩
    · simp [Database.table, Catalog.tableAt_createTable_above _ _ _ above] at found

end Belay.Sqlite.Model
