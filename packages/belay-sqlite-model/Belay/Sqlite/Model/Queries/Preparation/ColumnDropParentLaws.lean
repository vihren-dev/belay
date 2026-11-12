import Belay.Sqlite.Model.Shared.Catalog.ParentKeys

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every test, indexed map and list: if the map keeps the result of the test, the first item that passes
the test in the mapped list is the first item in the list that passes it, mapped, at the same place. Proof
sketch: induction over the list, with the shifted map for the tail ({lit}`List.mapIdx_cons`). -/
theorem findPosition_mapIdx {α : Type} (test : α → Bool) (move : Nat → α → α)
    (same : ∀ slot item, test (move slot item) = test item) (items : List α) :
    findPosition test (items.mapIdx move) = (findPosition test items).map fun (slot, item) => (slot, move slot item) := by
  induction items generalizing move with
  | nil => simp [findPosition]
  | cons item rest ih =>
    have tail := ih (fun slot => move (slot + 1)) (fun slot other => same (slot + 1) other)
    rw [List.mapIdx_cons]
    simp only [findPosition, same 0 item]
    by_cases passes : test item = true
    · simp [passes]
    · simp [passes, tail, Option.map_map, Function.comp_def]

/-- For every test and list: the item that {lit}`findPosition` finds is at the place that it gives and passes the
test. Proof sketch: induction over the list. -/
theorem findPosition_spec {α : Type} (test : α → Bool) (items : List α) {slot : Nat} {item : α}
    (found : findPosition test items = some (slot, item)) : items[slot]? = some item ∧ test item = true := by
  induction items generalizing slot with
  | nil => simp [findPosition] at found
  | cons head rest ih =>
    simp only [findPosition] at found
    by_cases passes : test head = true
    · simp only [passes, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      simpa using passes
    · simp only [passes, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff, Prod.exists] at found
      obtain ⟨before, found', inRest, rfl, rfl⟩ := found
      have := ih inRest
      simpa using this

end Belay.Sqlite.Model
