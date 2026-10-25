import Belay.Sqlite.Model.CatalogValidSet
import Belay.Sqlite.Model.KeysUniqueAddColumn
import Belay.Sqlite.Model.ForeignKeyFacts

set_option doc.verso true

/-! ADD COLUMN and the name search of a catalog. The replaced table keeps its name and kind, so a
search by name finds the same position, and the parent indexes of any position are unchanged. -/

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

/-- For every catalog, target, column and name: the table found by name after
{name}`Catalog.addColumn` is the table found before, at the same position, with the column
appended when that position is the target. A catalog without a table at the target is unchanged.
Proof sketch: the replaced object keeps its name and kind, so the first-match search finds the
same position ({name}`findPosition_set_same`). -/
theorem Catalog.findTable_addColumn (catalog : Catalog) (target : Nat) (column : CatalogColumn) (name : Identifier) :
    (catalog.addColumn target column).findTable name = (catalog.findTable name).map fun (position, shape) =>
      (position, if position = target ∧ (catalog.tableAt target).isSome then
        {shape with columns := shape.columns ++ [column]} else shape) := by
  unfold Catalog.addColumn
  cases atTarget : catalog[target]? with
  | none =>
    have none : catalog.tableAt target = none := by simp [Catalog.tableAt, atTarget]
    simp [none]
  | some object =>
    obtain ⟨objectName, entry⟩ := object
    cases entry with
    | table shape =>
      have present : catalog.tableAt target = some shape := by simp [Catalog.tableAt, atTarget]
      simp only [Catalog.findTable, Catalog.find, present, Option.isSome_some, and_true]
      rw [findPosition_set_same _ _ catalog target _ atTarget (by simp [CatalogEntry.isTrigger, CatalogObject.isTrigger])]
      cases found : findPosition (fun object => object.name.sameName name && !object.isTrigger) catalog with
      | none => simp
      | some pair =>
        obtain ⟨index, object⟩ := pair
        by_cases here : index = target
        · subst here
          obtain ⟨atIndex, _, _⟩ := (findPosition_eq_some_iff _ _ _ _).mp found
          rw [atTarget, Option.some.injEq] at atIndex
          subst atIndex
          simp
        · obtain ⟨_, entry⟩ := object
          cases entry <;> simp [here]
    | index _ | trigger _ =>
      have none : catalog.tableAt target = none := by simp [Catalog.tableAt, atTarget]
      simp [none]

/-- For every function that gives none for each table entry, catalog, target and column: the
objects that the function keeps are the same after {name}`Catalog.addColumn`. Proof sketch: ADD
COLUMN replaces a table entry by a table entry ({name}`filterMap_set_none`). -/
theorem Catalog.filterMap_addColumn {β} (function : CatalogObject → Option β)
    (tables : ∀ name table, function {name, entry := .table table} = none) (catalog : Catalog) (target : Nat)
    (column : CatalogColumn) : (catalog.addColumn target column).filterMap function = catalog.filterMap function := by
  unfold Catalog.addColumn
  split
  · rename_i name table found
    exact filterMap_set_none function _ (tables _ _) catalog target (by simp [found, tables])
  all_goals rfl

/-- For every catalog, two positions, column and table entry: the parent indexes of a position for
the entry ({name}`Catalog.parentIndexes`) are the same after {name}`Catalog.addColumn`. Proof
sketch: the entry is an argument, and the catalog adds to the parent indexes only its indexes
({name}`Catalog.filterMap_addColumn`). -/
theorem Catalog.parentIndexes_addColumn (catalog : Catalog) (target position : Nat) (column : CatalogColumn)
    (shape : CatalogTable) :
    (catalog.addColumn target column).parentIndexes position shape = catalog.parentIndexes position shape := by
  unfold Catalog.parentIndexes
  rw [Catalog.filterMap_addColumn _ (fun _ _ => rfl)]

end Belay.Sqlite.Model
