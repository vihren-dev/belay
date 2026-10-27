import Belay.Sqlite.Model.Resolution.ColumnDropSpec
import Belay.Sqlite.Model.Resolution.ParentKeys

set_option doc.verso true

/-! The tables of the catalog after ALTER TABLE DROP COLUMN (ADR 0019, D4): the table at the position has
lost the column, and every other table is as it was. -/

namespace Belay.Sqlite.Model

/-- For every catalog, position, index and slot: the object of the catalog after the drop at the slot is the
object before it, changed by {lit}`CatalogObject.dropColumn`. Proof sketch: {lit}`List.getElem?_mapIdx`. -/
theorem Catalog.dropColumn_getElem? (catalog : Catalog) (position index slot : Nat) :
    (catalog.dropColumn position index)[slot]? =
      catalog[slot]?.map (CatalogObject.dropColumn position index slot) := by
  simp [Catalog.dropColumn, List.getElem?_mapIdx]

/-- For every catalog, position and index: the catalog after the drop has as many objects as before. Proof
sketch: {lit}`List.length_mapIdx`. -/
theorem Catalog.length_dropColumn (catalog : Catalog) (position index : Nat) :
    (catalog.dropColumn position index).length = catalog.length := by
  simp [Catalog.dropColumn]

/-- For every catalog, position, index and table: if the catalog has the table at the position, the catalog
after the drop has the table without the column at the position. Proof sketch:
{name}`Catalog.dropColumn_getElem?` and the entry of the object. -/
theorem Catalog.tableAt_dropColumn_same {catalog : Catalog} {position index : Nat} {table : CatalogTable}
    (found : catalog.tableAt position = some table) :
    (catalog.dropColumn position index).tableAt position = some (table.dropColumnAt index) := by
  unfold Catalog.tableAt at found ⊢
  rw [Catalog.dropColumn_getElem?]
  rcases hold : catalog[position]? with _ | ⟨name, entry⟩
  · simp [hold] at found
  · cases entry <;> simp_all [CatalogObject.dropColumn]

/-- For every catalog, two different positions, and index: the table of the catalog after the drop at the
other position is the table of the catalog before it. Proof sketch: {name}`Catalog.dropColumn_getElem?`;
an index at the position stays an index, and the other objects stay. -/
theorem Catalog.tableAt_dropColumn_other (catalog : Catalog) {position other : Nat} (index : Nat)
    (different : other ≠ position) :
    (catalog.dropColumn position index).tableAt other = catalog.tableAt other := by
  unfold Catalog.tableAt
  rw [Catalog.dropColumn_getElem?]
  rcases hold : catalog[other]? with _ | ⟨name, entry⟩
  · simp
  · cases entry <;> simp_all [CatalogObject.dropColumn]

/-- For every catalog, position and index that pass {name}`Catalog.droppable`: the catalog has a table at the
position, and that table gives the facts of {name}`CatalogTable.DropsCleanly`; no index of the catalog reads the
column. Proof sketch: unfold the test, and use {name}`CatalogTable.droppable_spec`. -/
theorem Catalog.droppable_spec {catalog : Catalog} {position index : Nat} (ok : catalog.droppable position index = true) :
    ∃ table, catalog.tableAt position = some table ∧ table.DropsCleanly index ∧
      ∀ object ∈ catalog, ∀ definition, object.entry = .index definition →
        definition.readsColumn position index = false := by
  unfold Catalog.droppable at ok
  rcases hold : catalog[position]? with _ | ⟨name, entry⟩
  · simp [hold] at ok
  · cases entry with
    | table table =>
      simp only [hold, Bool.and_eq_true] at ok
      refine ⟨table, by simp [Catalog.tableAt, hold], CatalogTable.droppable_spec ok.1, ?_⟩
      intro object member definition same
      have := List.all_eq_true.mp ok.2 object member
      simpa [CatalogObject.allowsDrop, same] using this
    | index _ | view _ | trigger _ => simp [hold] at ok

end Belay.Sqlite.Model
