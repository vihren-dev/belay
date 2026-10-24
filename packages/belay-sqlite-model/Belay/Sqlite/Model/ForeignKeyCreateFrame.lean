import Belay.Sqlite.Model.ForeignKeyRowFrame
import Belay.Sqlite.Model.KeysUniqueCreate

set_option doc.verso true

/-! CREATE appends an empty object. Row comparisons stay fixed; new declarations and
changed parent selection have separate schema obligations. -/
namespace Belay.Sqlite.Model

/-- For every aligned database, appended object and position, appending the object with
an empty row list preserves the visible rows at that position. A new table has no rows.
Proof sketch: an old table stays identical; every other resulting table is empty. -/
theorem Database.rowsAt_appendEmpty (database : Database)
    (aligned : database.rows.length = database.catalog.length) (object : CatalogObject) (position : Nat) :
    ({catalog := database.catalog ++ [object], rows := database.rows ++ [[]]} : Database).rowsAt position =
      database.rowsAt position := by
  cases old : database.table position with
  | some table =>
    have kept := database.table_append object old
    simp only [Database.rowsAt, old, kept]
  | none =>
    cases fresh : ({catalog := database.catalog ++ [object], rows := database.rows ++ [[]]} : Database).table position with
    | none => simp only [Database.rowsAt, old, fresh]
    | some table =>
      rcases Database.table_append_cases aligned object fresh with found | empty
      · rw [old] at found; cases found
      · simp only [Database.rowsAt, old, fresh, Option.map_some, Option.getD_some, Option.map_none, Option.getD_none, empty]

/-- For every aligned database, object, supplied link and child row, appending the object
with empty storage leaves the supplied comparison unchanged. This includes links to absent
positions: a newly created parent table is empty too. Supporting indexes and the catalog's
choice of a new link are irrelevant. Proof sketch: preserve existing parent tables and rows;
when the old parent is absent, any new parent has no rows, so both tests use only NULL cells. -/
theorem ForeignKeyLink.satisfied_appendEmpty (database : Database)
    (aligned : database.rows.length = database.catalog.length) (object : CatalogObject)
    (link : ForeignKeyLink) (row : Row) :
    link.satisfied {catalog := database.catalog ++ [object], rows := database.rows ++ [[]]} row =
      link.satisfied database row := by
  cases selected : link.parent with
  | missing | mismatch => simp only [ForeignKeyLink.satisfied, selected]
  | located position comparison =>
    have rows := database.rowsAt_appendEmpty aligned object position
    cases shape : database.catalog.tableAt position with
    | some shape =>
      have kept := Catalog.tableAt_append object shape
      simp only [ForeignKeyLink.satisfied, selected, shape, kept, rows]
    | none =>
      have empty : database.rowsAt position = [] := by simp only [Database.rowsAt, Database.table, shape, Option.map_none, Option.getD_none]
      cases fresh : (database.catalog ++ [object]).tableAt position <;>
        simp only [ForeignKeyLink.satisfied, selected, shape, fresh, rows, empty, parentFound, List.any_nil, Bool.or_false]
      all_goals cases comparison <;> simp_all only [Option.any_none, Bool.or_false]
      all_goals split <;> exact Bool.or_false _

/-- For any aligned database with row references under a supplied mapping, appending an
object with no rows preserves row references under a new mapping that agrees on every old
declaration. New declarations need no row premise because the new table is empty. Parent-key
selection may change. Proof sketch: old child rows use the unchanged supplied comparison;
new tables have no child rows to check. -/
theorem Database.RowReferencesHold.appendEmpty {database : Database} {mapping nextMapping : ForeignKeyMapping}
    (holds : database.RowReferencesHold mapping) (aligned : database.rows.length = database.catalog.length)
    (object : CatalogObject)
    (same : ∀ position table, database.table position = some table → ∀ key ∈ table.shape.allForeignKeys,
      nextMapping.parent position key = mapping.parent position key) :
    ({catalog := database.catalog ++ [object], rows := database.rows ++ [[]]} : Database).RowReferencesHold nextMapping := by
  intro position table found key declared row member
  rcases Database.table_append_cases aligned object found with old | empty
  · have link : nextMapping.link position key = mapping.link position key := by
      simp only [ForeignKeyMapping.link, same position table old key declared]
    rw [link, ForeignKeyLink.satisfied_appendEmpty database aligned object]
    exact holds position table old key declared row member
  · rw [empty] at member; cases member

/-- Any table found after appending one catalog object is an old table at the same position,
or is exactly the appended table at the old catalog length. An index or trigger adds no table.
Proof sketch: split the position below the old length or into the singleton suffix. -/
theorem Catalog.tableAt_append_cases {catalog : Catalog} {object : CatalogObject} {position : Nat} {shape : CatalogTable}
    (found : (catalog ++ [object]).tableAt position = some shape) :
    catalog.tableAt position = some shape ∨ position = catalog.length ∧ object.entry = .table shape := by
  by_cases below : position < catalog.length
  · left
    simpa only [Catalog.tableAt, List.getElem?_append_left below] using found
  · right
    unfold Catalog.tableAt at found
    rw [List.getElem?_append_right (Nat.le_of_not_lt below)] at found
    cases rest : position - catalog.length with
    | zero =>
      refine ⟨by omega, ?_⟩
      rw [rest] at found
      cases object with
      | mk name entry =>
        cases entry <;> simp_all
    | succ n => simp [rest] at found

/-- For any database with compatible schemas, appending an object preserves compatibility
under a new mapping when it agrees on old declarations, old parent selection is unchanged,
and each newly declared key has a located mapping equal to the extended catalog's selection.
The last premise is empty for indexes, triggers and tables without foreign keys. Stored rows
are unrestricted. Proof sketch: reuse each old declaration's schema fact; a newly appended
table uses the explicit facts about its new keys. -/
theorem Database.ParentSchemasCompatible.appendEmpty {database : Database} {mapping nextMapping : ForeignKeyMapping}
    (holds : database.ParentSchemasCompatible mapping) (object : CatalogObject)
    (same : ∀ position table, database.table position = some table → ∀ key ∈ table.shape.allForeignKeys,
      nextMapping.parent position key = mapping.parent position key)
    (selection : ∀ position table, database.table position = some table → ∀ key ∈ table.shape.allForeignKeys,
      (database.catalog ++ [object]).parentLink key = database.catalog.parentLink key)
    (newKeys : ∀ shape, object.entry = .table shape → ∀ key ∈ shape.allForeignKeys,
      (nextMapping.parent database.catalog.length key).isLocated = true ∧
      nextMapping.parent database.catalog.length key = (database.catalog ++ [object]).parentLink key) :
    ({catalog := database.catalog ++ [object], rows := database.rows ++ [[]]} : Database).ParentSchemasCompatible nextMapping := by
  intro position table found key declared
  obtain ⟨shape, atShape, equal⟩ := Option.map_eq_some_iff.mp found
  subst table
  rcases Catalog.tableAt_append_cases atShape with old | ⟨rfl, fresh⟩
  · have oldTable : database.table position = some {shape, rows := database.rows.getD position []} := by
      simp only [Database.table, old, Option.map_some]
    rw [same position _ oldTable key declared, selection position _ oldTable key declared]
    exact holds position _ oldTable key declared
  · exact newKeys shape fresh key declared

end Belay.Sqlite.Model
