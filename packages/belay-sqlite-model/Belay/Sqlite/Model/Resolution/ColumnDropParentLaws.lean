import Belay.Sqlite.Model.Resolution.ColumnDropKeyLaws
import Belay.Sqlite.Model.Resolution.ParentKeys

set_option doc.verso true

/-! What a foreign key finds after ALTER TABLE DROP COLUMN (ADR 0019, D4): a foreign key that does not name
the table with the dropped column finds the same parent table, with the same parent key, as before. The drop
changes only the table at the position and the indexes of that table, and the lookup of a parent by the name
of another table reads neither. -/

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

/-- For every two names: the names are the same in one order exactly when they are the same in the other. Proof
sketch: the comparison is equality of the folded names, which is symmetric. -/
theorem Identifier.sameName_comm (left right : Identifier) : left.sameName right = right.sameName left := by
  unfold Identifier.sameName
  by_cases same : left.folded = right.folded
  · simp [same]
  · have different : ¬ right.folded = left.folded := fun h => same h.symm
    rw [beq_eq_false_iff_ne.mpr same, beq_eq_false_iff_ne.mpr different]

/-- For every position, index, slot and object: the drop keeps the name of the object. Proof sketch: only a table
at the dropped position changes, and only in its entry. -/
@[simp] theorem CatalogObject.name_dropColumn (position index slot : Nat) (object : CatalogObject) :
    (object.dropColumn position index slot).name = object.name := by
  rcases object with ⟨name, entry⟩
  cases entry with
  | table _ => by_cases at_position : slot = position <;> simp [CatalogObject.dropColumn, at_position]
  | index _ | view _ | trigger _ => simp [CatalogObject.dropColumn]

/-- For every position, index, slot and object: the object after the drop is a trigger exactly when the object is
a trigger. The formula says nothing about the other kinds of object. Proof sketch: the drop changes only the entry
of a table or an index, and neither is a trigger. -/
@[simp] theorem CatalogObject.isTrigger_dropColumn (position index slot : Nat) (object : CatalogObject) :
    (object.dropColumn position index slot).isTrigger = object.isTrigger := by
  rcases object with ⟨name, entry⟩
  cases entry with
  | table _ =>
    by_cases at_position : slot = position <;>
      simp [CatalogObject.dropColumn, CatalogObject.isTrigger, CatalogEntry.isTrigger, at_position]
  | index _ | view _ | trigger _ => simp [CatalogObject.dropColumn, CatalogObject.isTrigger, CatalogEntry.isTrigger]

/-- For every catalog, indexed change of objects that keeps the name and whether each object is a trigger, and name: the
first table, view or index with the name in the changed catalog is the first one in the catalog, at the same
place, with the change applied. The lookup skips triggers, so a rewrite that keeps names and the trigger test keeps
every lookup by name; the formula does not distinguish tables, views and indexes. Proof sketch: {name}`findPosition_mapIdx`. -/
theorem Catalog.find_mapIdx (catalog : Catalog) (move : Nat → CatalogObject → CatalogObject)
    (name : ∀ slot object, (move slot object).name = object.name)
    (trigger : ∀ slot object, (move slot object).isTrigger = object.isTrigger) (lookup : Identifier) :
    Catalog.find (catalog.mapIdx move) lookup =
      (catalog.find lookup).map fun (slot, object) => (slot, move slot object) := by
  unfold Catalog.find
  exact findPosition_mapIdx _ _ (fun slot object => by simp [name, trigger]) catalog

/-- For every catalog, position, index and name: the first table, view or index with the name in the catalog
after the drop is the one that is first before it, at the same place, with the drop applied. Proof sketch: the
instance of {name}`Catalog.find_mapIdx` for {name}`CatalogObject.dropColumn`, which keeps names and kinds. -/
theorem Catalog.find_dropColumn (catalog : Catalog) (position index : Nat) (name : Identifier) :
    (catalog.dropColumn position index).find name =
      (catalog.find name).map fun (slot, object) => (slot, object.dropColumn position index slot) :=
  Catalog.find_mapIdx catalog _ (fun _ _ => by simp) (fun _ _ => by simp) name

/-- For every catalog, two different positions, index, table and key: the indexes of the table at the other
position that a parent key can use are the same after the drop. Proof sketch: an object stays as it is unless it
is the table at the dropped position or an index of that table, and neither is an index of the other table. -/
theorem Catalog.parentIndexes_dropColumn_other (catalog : Catalog) {position other : Nat} (index : Nat)
    (table : CatalogTable) (different : other ≠ position) :
    (catalog.dropColumn position index).parentIndexes other table = catalog.parentIndexes other table := by
  have key := List.filterMap_mapIdx_eq_map catalog (CatalogObject.dropColumn position index)
    (fun object => match object.entry with
      | .index definition =>
        if definition.table != other || !definition.unique || definition.filter.isSome then none
        else (definition.keys.mapM fun (key : IndexKey) => match key.term with
          | .column column => some (column, key.collation)
          | .expression _ => none).map (false, ·)
      | .table _ | .view _ | .trigger _ => none)
    (fun object => match object.entry with
      | .index definition =>
        if definition.table != other || !definition.unique || definition.filter.isSome then none
        else (definition.keys.mapM fun (key : IndexKey) => match key.term with
          | .column column => some (column, key.collation)
          | .expression _ => none).map (false, ·)
      | .table _ | .view _ | .trigger _ => none) id ?_
  · rw [List.map_id] at key
    unfold Catalog.parentIndexes Catalog.dropColumn
    dsimp only
    congr 1
  · intro slot object
    rcases object with ⟨name, entry⟩
    cases entry with
    | table _ => by_cases at_position : slot = position <;> simp [CatalogObject.dropColumn, at_position]
    | index definition =>
      by_cases onTable : definition.table = position
      · simp [CatalogObject.dropColumn, CatalogIndex.dropColumn, onTable, Ne.symm different]
      · simp [CatalogObject.dropColumn, onTable, CatalogIndex.dropColumn]
    | view _ => simp [CatalogObject.dropColumn]
    | trigger _ => simp [CatalogObject.dropColumn]

/-- For every catalog, position, index, object at the position and foreign key: if the key does not name the
object by its table name, the parent that the key finds after the drop is the parent that it finds before it.
Proof sketch: the first object with the name of the key is at the same place after the drop
({name}`Catalog.find_dropColumn`) and is not at the dropped position, where the name does not fit; there it is
unchanged unless it is an index, which no parent lookup uses, and its parent indexes are the same
({name}`Catalog.parentIndexes_dropColumn_other`). -/
theorem Catalog.parentLink_dropColumn (catalog : Catalog) {position : Nat} (index : Nat) {object : CatalogObject}
    (at_position : catalog[position]? = some object) (key : ForeignKey)
    (other : key.table.sameName object.name = false) :
    (catalog.dropColumn position index).parentLink key = catalog.parentLink key := by
  have found := Catalog.find_dropColumn catalog position index key.table
  have keyed : ∀ slot, Catalog.parentKey (catalog.dropColumn position index) slot = Catalog.parentKey catalog slot ∨
      slot = position := by
    intro slot
    by_cases same : slot = position
    · exact Or.inr same
    · refine Or.inl ?_
      funext parent key
      unfold Catalog.parentKey
      rw [Catalog.parentIndexes_dropColumn_other catalog index parent same]
  unfold Catalog.parentLink Catalog.findTable Catalog.findView
  rcases hold : catalog.find key.table with _ | ⟨slot, found_object⟩
  · simp [found, hold]
  · have spec := findPosition_spec _ catalog (show findPosition _ catalog = some (slot, found_object) from hold)
    have different : slot ≠ position := by
      intro same
      subst same
      rw [at_position] at spec
      obtain ⟨same_object, named⟩ := spec
      cases Option.some.inj same_object
      simp only [Bool.and_eq_true] at named
      rw [Identifier.sameName_comm] at other
      simp [named.1] at other
    rcases found_object with ⟨name, entry⟩
    cases entry with
    | table parent =>
      rw [found, hold]
      simp only [Option.map_some, CatalogObject.dropColumn, different, ↓reduceIte]
      rcases keyed slot with same | same
      · rw [same]
      · exact absurd same different
    | index _ => simp [found, hold, CatalogObject.dropColumn]
    | view _ => simp [found, hold, CatalogObject.dropColumn]
    | trigger _ => simp [found, hold, CatalogObject.dropColumn]

end Belay.Sqlite.Model
