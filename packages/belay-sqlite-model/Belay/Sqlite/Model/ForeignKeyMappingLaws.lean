import Belay.Sqlite.Model.ForeignKeyFacts

set_option doc.verso true

/-! Connect supplied foreign-key mappings with the links that catalog resolution selects,
so pragma and row-engine proofs can use the public row-reference atom. -/

namespace Belay.Sqlite.Model

/-- A link belongs to the catalog's child links at a position exactly when its child is that
position, its key is declared by that table, and its parent is the catalog's selection.
No link belongs at a position without a table. Proof sketch: unpack the catalog traversal,
then identify the position from its indexed entry. -/
theorem Catalog.mem_childLinks_iff (catalog : Catalog) (position : Nat) (link : ForeignKeyLink) :
    link ∈ childLinks catalog.foreignKeyLinks position ↔
      link.child = position ∧ link.parent = catalog.parentLink link.key ∧
        ∃ shape, catalog.tableAt position = some shape ∧ link.key ∈ shape.allForeignKeys := by
  simp only [childLinks, List.mem_reverse, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨member, child⟩
    obtain ⟨⟨object, place⟩, atPlace, member⟩ := List.mem_flatMap.mp member
    have entry := List.mem_zipIdx_iff_getElem?.mp atPlace
    rcases object with ⟨name, objectEntry⟩
    cases kind : objectEntry with
    | index _ | view _ => simp [kind] at member
    | trigger _ => simp [kind] at member
    | table shape =>
      simp only [kind, List.mem_map] at member
      obtain ⟨key, declared, same⟩ := member
      subst link
      simp only at child
      subst place
      exact ⟨rfl, rfl, shape, by simp [Catalog.tableAt, entry, kind], declared⟩
  · rintro ⟨child, parent, shape, atShape, declared⟩
    refine ⟨?_, child⟩
    unfold Catalog.tableAt at atShape
    cases entry : catalog[position]? with
    | none => simp [entry] at atShape
    | some object =>
      rcases object with ⟨name, objectEntry⟩
      cases kind : objectEntry with
      | index _ | view _ => simp [entry, kind] at atShape
      | trigger _ => simp [entry, kind] at atShape
      | table found =>
        have same : found = shape := by simpa [entry, kind] using atShape
        subst found
        apply List.mem_flatMap.mpr
        refine ⟨({ name, entry := .table shape }, position), List.mem_zipIdx_iff_getElem?.mpr (by simpa [kind] using entry), ?_⟩
        simp only [List.mem_map]
        refine ⟨link.key, declared, ?_⟩
        cases link
        simp_all

/-- For every database, position and table present there, the row fact with the selected
mapping says exactly that each engine child link is satisfied by every stored row. Proof
sketch: each catalog link corresponds to one declared key, and both use the same parent. -/
theorem Table.rowReferencesHold_selected_iff (database : Database) (position : Nat) (table : Table)
    (present : database.table position = some table) :
    table.RowReferencesHold database.catalog.foreignKeyMapping database position ↔
      ∀ link ∈ childLinks database.catalog.foreignKeyLinks position, ∀ row ∈ table.rows,
        link.satisfied database row = true := by
  have shape : database.catalog.tableAt position = some table.shape := by
    unfold Database.table at present
    obtain ⟨shape, atShape, rfl⟩ := Option.map_eq_some_iff.mp present
    exact atShape
  constructor
  · intro holds link member row inRows
    obtain ⟨child, selected, found, atFound, declared⟩ :=
      (database.catalog.mem_childLinks_iff position link).mp member
    have same : found = table.shape := Option.some.inj (atFound.symm.trans shape)
    subst found
    rw [← ForeignKeyMapping.selected_satisfied database link row selected, child]
    exact holds link.key declared row inRows
  · intro holds key declared row inRows
    apply holds (database.catalog.foreignKeyMapping.link position key) ?_ row inRows
    apply (database.catalog.mem_childLinks_iff position _).mpr
    exact ⟨rfl, rfl, table.shape, shape, declared⟩

end Belay.Sqlite.Model
