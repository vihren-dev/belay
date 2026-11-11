import Belay.Sqlite.Model.Queries.Preparation.ColumnSpec
import Belay.Sqlite.Model.Shared.Catalog.Catalog

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every test, replacement, list and position that holds an element with the same test
result as the replacement: searching the list with the element replaced finds the same position,
with the replacement when that position is the replaced one. Proof sketch: induction on the list;
the head either passes the test or the search continues with the tail. -/
theorem findPosition_set_same {α} (test : α → Bool) (replacement : α) :
    ∀ (items : List α) (position : Nat) (old : α), items[position]? = some old → test replacement = test old →
      findPosition test (items.set position replacement) =
        (findPosition test items).map fun (index, item) => (index, if index = position then replacement else item)
  | [], _, _, present, _ => by simp at present
  | head :: rest, 0, old, present, same => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at present
    subst present
    by_cases passes : test head = true
    · simp [findPosition, passes, same]
    · have fails : test head = false := by simpa using passes
      have failsNew : test replacement = false := by rw [same, fails]
      simp [findPosition, fails, failsNew, Option.map_map, Function.comp_def]
  | head :: rest, position + 1, old, present, same => by
    by_cases passes : test head = true
    · simp [findPosition, passes]
    · have fails : test head = false := by simpa using passes
      have inner := findPosition_set_same test replacement rest position old (by simpa using present) same
      simp [findPosition, fails, inner, Option.map_map, Function.comp_def]

/-- For every catalog, target, column and name: the view found by name after {name}`Catalog.addColumn`
is the view found before. The replaced object is a table that keeps its name, so a name that finds a
view finds the same view, and a name that finds a table or nothing finds no view. Proof sketch: the
first-match search finds the same position ({name}`findPosition_set_same`), and the object there is a
view only if it was not the replaced table. -/
theorem Catalog.findView_addColumn (catalog : Catalog) (target : Nat) (column : CatalogColumn) (name : Identifier) :
    (catalog.addColumn target column).findView name = catalog.findView name := by
  unfold Catalog.addColumn
  split
  · rename_i objectName table atTarget
    unfold Catalog.findView Catalog.find
    rw [findPosition_set_same _ _ catalog target _ atTarget (by simp [CatalogEntry.isTrigger, CatalogObject.isTrigger])]
    cases located : findPosition (fun object => object.name.sameName name && !object.isTrigger) catalog with
    | none => rfl
    | some pair =>
      obtain ⟨index, object⟩ := pair
      by_cases here : index = target
      · subst here
        obtain ⟨atIndex, _, _⟩ := (findPosition_eq_some_iff _ _ _ _).mp located
        rw [atTarget, Option.some.injEq] at atIndex
        subst atIndex
        simp
      · obtain ⟨_, entry⟩ := object
        cases entry <;> simp [here]
  all_goals rfl

end Belay.Sqlite.Model
