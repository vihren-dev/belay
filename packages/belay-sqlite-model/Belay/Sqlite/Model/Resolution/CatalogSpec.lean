import Belay.Sqlite.Model.Resolution.ColumnSpec
import Belay.Sqlite.Model.Resolution.CatalogDrop

set_option doc.verso true

/-! The unique-names rule of the catalog, and the theorems that resolution keeps it. -/

namespace Belay.Sqlite.Model

/-- For every test and list, {name}`findPosition` finds nothing exactly when every
element fails the test. Proof sketch: induction on the list; a passing head is found
at position zero, and a failing head leaves the search to the tail. -/
theorem findPosition_eq_none_iff (test : α → Bool) (items : List α) :
    findPosition test items = none ↔ ∀ item ∈ items, test item = false := by
  induction items with
  | nil => simp [findPosition]
  | cons head rest ih =>
    by_cases passes : test head = true
    · simp [findPosition, passes]
    · simp [findPosition, passes, ih]

/-- For every catalog and name, {name}`Catalog.find` finds nothing exactly when the
folded name is not among the catalog's folded names. Proof sketch: rewrite with
{name}`findPosition_eq_none_iff`; the folded-name test fails for every object exactly
when the folded name is not in the mapped list. -/
theorem Catalog.find_eq_none_iff (catalog : Catalog) (name : Identifier) :
    catalog.find name = none ↔ name.folded ∉ catalog.foldedNames := by
  rw [Catalog.find, findPosition_eq_none_iff, Catalog.foldedNames]
  constructor
  · intro all named
    obtain ⟨object, kept, same⟩ := List.mem_map.mp named
    obtain ⟨member, live⟩ := List.mem_filter.mp kept
    have := all object member
    simp_all [Identifier.sameName]
  · intro absent object member
    cases trigger : object.isTrigger
    · have different : object.name.folded ≠ name.folded := fun same =>
        absent (List.mem_map.mpr ⟨object, List.mem_filter.mpr ⟨member, by simp [trigger]⟩, same⟩)
      simp [Identifier.sameName, different]
    · simp

/-- For every catalog, name, position and object that {name}`Catalog.find` returns, the object
is not a trigger: triggers have a namespace of their own. Proof sketch:
{name}`findPosition_eq_some_iff` gives the lookup test of the found object, and its second
conjunct is that the object is not a trigger. -/
theorem Catalog.find_not_trigger (catalog : Catalog) (name : Identifier) (position : Nat) (object : CatalogObject)
    (found : catalog.find name = some (position, object)) : object.isTrigger = false := by
  have ⟨_, test, _⟩ := (findPosition_eq_some_iff _ _ _ _).mp found
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at test
  exact test.2

/-- For every catalog, name, position and table entry that {name}`Catalog.findTable`
returns, the catalog has an object at that position with the table entry, whose
folded name is the folded given name. Proof sketch: the result comes from
{name}`Catalog.find`, and {name}`findPosition_eq_some_iff` gives the object at the
position and its passing name test. -/
theorem Catalog.findTable_some (catalog : Catalog) (name : Identifier) (position : Nat) (table : CatalogTable)
    (found : catalog.findTable name = some (position, table)) :
    ∃ object, catalog[position]? = some object ∧ object.entry = .table table ∧
      object.name.folded = name.folded := by
  unfold Catalog.findTable at found
  split at found <;> try contradiction
  rename_i object_position object_name hfind
  cases found
  have ⟨atPosition, test, _⟩ := (findPosition_eq_some_iff _ _ _ _).mp hfind
  simp only [Identifier.sameName, Bool.and_eq_true, beq_iff_eq] at test
  exact ⟨_, atPosition, rfl, test.1⟩

/-- For every successful view lookup, its catalog position contains that view
definition. Proof sketch: unpack the shared named-object search and recover its
position with {name}`findPosition_eq_some_iff`. -/
theorem Catalog.findView_some {catalog : Catalog} {name : Identifier} {position : Nat}
    {view : CatalogView} (found : catalog.findView name = some (position, view)) :
    ∃ object, catalog[position]? = some object ∧ object.entry = .view view := by
  unfold Catalog.findView at found
  split at found <;> try contradiction
  rename_i place declared hfind
  cases found
  obtain ⟨atPosition, _, _⟩ := (findPosition_eq_some_iff _ _ _ _).mp hfind
  exact ⟨_, atPosition, rfl⟩

/-- How one statement may change the catalog. The catalog is the same; or one object
is appended whose name {name}`Catalog.find` does not find; or a trigger is appended, whose
name is in a namespace of its own; or the object at a position is replaced by one with the
same name and kind; or the objects at some positions are removed ({name}`Catalog.drop`). -/
inductive CatalogStep (catalog : Catalog) : Catalog → Prop where
  /-- The catalog does not change. -/
  | same : CatalogStep catalog catalog
  /-- One object with an unused name is appended. -/
  | append (object : CatalogObject) (unused : catalog.find object.name = none) :
      CatalogStep catalog (catalog ++ [object])
  /-- One trigger is appended (ADR 0018, D5). -/
  | appendTrigger (object : CatalogObject) (trigger : object.isTrigger = true) :
      CatalogStep catalog (catalog ++ [object])
  /-- The object at a position gets another entry and keeps its name. -/
  | replace (position : Nat) (object : CatalogObject) (entry : CatalogEntry)
      (atPosition : catalog[position]? = some object) (kind : entry.isTrigger = object.entry.isTrigger) :
      CatalogStep catalog (catalog.set position { name := object.name, entry := entry })
  /-- The objects at the positions are removed, as DROP does. -/
  | remove (positions : List Nat) : CatalogStep catalog (catalog.drop positions)

/-- For all catalogs related by {name}`CatalogStep`, unique folded names before give
unique folded names after. Proof sketch: an unchanged catalog keeps its names; an
appended object has a folded name outside the list, by
{name}`Catalog.find_eq_none_iff`; a replaced object keeps its name, so the list of
folded names is the same; a removal keeps a sublist of the names
({name}`Catalog.NamesUnique.drop`). -/
theorem CatalogStep.namesUnique (step : CatalogStep catalog after) (unique : catalog.NamesUnique) :
    after.NamesUnique := by
  cases step with
  | same => exact unique
  | remove positions => exact unique.drop positions
  | append object unused =>
    have absent := (Catalog.find_eq_none_iff _ _).mp unused
    unfold Catalog.NamesUnique Catalog.foldedNames at *
    rw [List.filter_append, List.map_append]
    refine List.nodup_append.mpr ⟨unique, ?_, ?_⟩
    · cases kind : object.isTrigger <;> simp [List.filter, kind]
    · intro a inner b appended
      cases kind : object.isTrigger <;> simp [List.filter, kind] at appended
      subst appended
      obtain ⟨x, kept, named⟩ := List.mem_map.mp inner
      intro same
      exact absent (List.mem_map.mpr ⟨x, kept, named.trans same⟩)
  | appendTrigger object trigger =>
    unfold Catalog.NamesUnique Catalog.foldedNames at *
    simpa [List.filter, trigger] using unique
  | replace position object entry atPosition kind =>
    have names : Catalog.foldedNames (catalog.set position { name := object.name, entry := entry }) =
        catalog.foldedNames := by
      unfold Catalog.foldedNames
      obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp atPosition
      rw [List.set_eq_take_append_cons_drop]
      simp only [bound, ↓reduceIte]
      conv => rhs; rw [← List.take_append_drop position catalog, List.drop_eq_getElem_cons bound, value]
      simp only [List.filter_append, List.filter_cons, CatalogObject.isTrigger, kind, List.map_append]
      split <;> simp
    simpa [Catalog.NamesUnique, names] using unique

end Belay.Sqlite.Model
