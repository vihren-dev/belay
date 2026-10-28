import Belay.Sqlite.Model.Resolution.ColumnDropParentChildren
import Belay.Sqlite.Model.Resolution.ColumnDropCatalogLaws

set_option doc.verso true

/-! The foreign keys of a table after ALTER TABLE DROP COLUMN (ADR 0019, D4): every foreign key that stays is a
foreign key of the table before the drop, with the positions of its child columns changed, and it did not name the
dropped column. No table has the dropped table as the parent of a foreign key, so no key finds it as a parent. -/

namespace Belay.Sqlite.Model

/-- For every table that can lose the column at the index and every foreign key of the table without the column:
the table had a foreign key that did not name the column, and the foreign key is that one with the positions of its
child columns changed. Proof sketch: a key of a column that stays is a key of that column with its positions
changed, and so is a key of the table constraints; {name}`CatalogTable.DropsCleanly` says that none names the
column. -/
theorem CatalogTable.mem_allForeignKeys_dropColumnAt {table : CatalogTable} {index : Nat}
    (clean : table.DropsCleanly index) {key' : ForeignKey} (member : key' ∈ (table.dropColumnAt index).allForeignKeys) :
    ∃ key ∈ table.allForeignKeys, index ∉ key.columns ∧ key' = key.mapColumns (dropPosition index) := by
  unfold CatalogTable.allForeignKeys at member ⊢
  simp only [CatalogTable.dropColumnAt, List.mem_append, List.mem_flatMap, List.mem_map] at member
  rcases member with ⟨column', ⟨column, inColumns, rfl⟩, inKeys⟩ | ⟨key, inTable, rfl⟩
  · simp only [CatalogColumn.dropColumn, List.mem_map] at inKeys
    obtain ⟨key, inColumn, rfl⟩ := inKeys
    exact ⟨key, List.mem_append_left _ (List.mem_flatMap.mpr ⟨column, List.mem_of_mem_eraseIdx inColumns, inColumn⟩),
      clean.foreign column inColumns key inColumn, rfl⟩
  · exact ⟨key, List.mem_append_right _ inTable, clean.tableForeign key inTable, rfl⟩

/-- For every catalog, position, index and object at the position that pass {name}`Catalog.droppable`: no foreign
key of any table of the catalog names the object by its table name, so no key has the dropped table as its parent.
Proof sketch: the test {name}`CatalogObject.allowsDrop` holds for each object of the catalog. -/
theorem Catalog.droppable_foreign {catalog : Catalog} {position index : Nat} (ok : catalog.droppable position index = true)
    {object : CatalogObject} (at_position : catalog[position]? = some object) {slot : Nat} {table : CatalogTable}
    (found : catalog.tableAt slot = some table) {key : ForeignKey} (member : key ∈ table.allForeignKeys) :
    key.table.sameName object.name = false := by
  unfold Catalog.droppable at ok
  rw [at_position] at ok
  rcases object with ⟨name, entry⟩
  cases entry with
  | table dropped =>
    simp only [Bool.and_eq_true] at ok
    obtain ⟨other, inList⟩ : ∃ other, ({ name := other, entry := .table table } : CatalogObject) ∈ catalog := by
      unfold Catalog.tableAt at found
      rcases hold : catalog[slot]? with _ | ⟨n, e⟩
      · simp [hold] at found
      · cases e <;> simp_all
        exact ⟨n, List.mem_of_getElem? hold⟩
    have allowed := List.all_eq_true.mp ok.2 _ inList
    simp only [CatalogObject.allowsDrop, CatalogTable.hasParent, Bool.not_eq_true', List.any_eq_false] at allowed
    simpa using allowed key member
  | index _ | view _ | trigger _ => simp at ok

end Belay.Sqlite.Model
