import Belay.Sqlite.Model.Resolution.ColumnDropParentMapLaws

set_option doc.verso true

/-! Where a foreign key finds its parent, for the drop of a column (ADR 0019, D4). The parent table of a key is
not the table with the dropped column, and the child positions of a parent key are columns of the key. Both facts
let a proof move the child columns of a key without looking at the parent. -/

namespace Belay.Sqlite.Model

/-- For every function, predicate, list and result: if each result of the function has the property, each item of
a collected result has it. Proof sketch: induction over the list. -/
theorem List.mapM_option_mem {α β : Type} (step : α → Option β) (good : β → Prop)
    (kept : ∀ item value, step item = some value → good value) (items : List α) {values : List β}
    (collected : items.mapM step = some values) : ∀ value ∈ values, good value := by
  induction items generalizing values with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at collected
    subst collected
    simp
  | cons item rest ih =>
    simp only [List.mapM_cons] at collected
    cases first : step item with
    | none => simp [first] at collected
    | some value =>
      cases others : rest.mapM step with
      | none => simp [first, others] at collected
      | some tail =>
        simp [first, others] at collected
        subst collected
        intro member inList
        rcases List.mem_cons.mp inList with same | later
        · exact same ▸ kept item value first
        · exact ih others member later

/-- For every parent table, key and index: each child position of the pairs that the key names in an index is a
column of the key. Proof sketch: a pair takes its child from the columns of the key at the place of the referenced
name ({name}`List.mapM_option_mem`). -/
theorem matchIndex_children {parent : CatalogTable} {key : ForeignKey} {index : List (Nat × Collation)}
    {pairs : List (Nat × Nat)} (found : matchIndex parent key index = some pairs) :
    ∀ pair ∈ pairs, pair.1 ∈ key.columns := by
  unfold matchIndex at found
  by_cases lengths : (index.length != key.columns.length) = true
  · simp [lengths] at found
  · simp only [lengths, Bool.false_eq_true, ↓reduceIte] at found
    refine List.mapM_option_mem _ (fun pair => pair.1 ∈ key.columns) ?_ index found
    intro entry value step
    obtain ⟨column, collation⟩ := entry
    cases definition : parent.columns[column]? with
    | none => simp [definition] at step
    | some definition' =>
      simp [definition] at step
      obtain ⟨_, step⟩ := step
      cases place : List.findIdx? (fun x => x.sameName definition'.name) key.referenced with
      | none => simp [place] at step
      | some found =>
        cases child : key.columns[found]? with
        | none => simp [place, child] at step
        | some value' =>
          simp [place, child] at step
          subst step
          exact List.mem_of_getElem? child

/-- For every indexes, child columns and key found by the primary key: the pairs pair the child columns with
parent columns, so each child position is a child column. Proof sketch: {lit}`List.of_mem_zip`. -/
theorem primaryKey_children (indexes : List (Bool × List (Nat × Collation))) (columns : List Nat) {found : ParentKey}
    (hold : ((indexes.find? (·.1)).bind fun entry =>
        if entry.2.length = columns.length then some (ParentKey.columns (columns.zip (entry.2.map (·.1)))) else none) =
      some found) : ∃ pairs, found = ParentKey.columns pairs ∧ ∀ pair ∈ pairs, pair.1 ∈ columns := by
  obtain ⟨entry, _, kept⟩ := Option.bind_eq_some_iff.mp hold
  by_cases lengths : entry.2.length = columns.length
  · simp only [lengths, ↓reduceIte, Option.some.injEq] at kept
    subst kept
    exact ⟨_, rfl, fun pair member => (List.of_mem_zip member).1⟩
  · simp [lengths] at kept

/-- For every indexes, parent table and key whose named index gives the parent key: each child position of its
pairs is a column of the key. Proof sketch: {name}`List.findSome?_eq_some_iff` and {name}`matchIndex_children`. -/
theorem namedKey_children (indexes : List (Bool × List (Nat × Collation))) (parent : CatalogTable) (key : ForeignKey)
    {found : ParentKey}
    (hold : indexes.findSome? (Option.map ParentKey.columns ∘ fun entry => matchIndex parent key entry.2) = some found) :
    ∃ pairs, found = ParentKey.columns pairs ∧ ∀ pair ∈ pairs, pair.1 ∈ key.columns := by
  obtain ⟨_, entry, _, _, chosen, _⟩ := List.findSome?_eq_some_iff.mp hold
  simp only [Function.comp_apply, Option.map_eq_some_iff] at chosen
  obtain ⟨pairs, matched, rfl⟩ := chosen
  exact ⟨pairs, rfl, matchIndex_children matched⟩

/-- For every catalog, position, parent table, key and parent key that the key finds: each child position that the
parent key selects for a link of the key is a column of the key. Proof sketch: the rowid key selects the first
column; the key of the primary key pairs the columns of the key with the parent columns
({lit}`List.of_mem_zip`); the pairs of a named index come from {name}`matchIndex_children`. -/
theorem Catalog.parentKey_children (catalog : Catalog) (position : Nat) (parent : CatalogTable) (key : ForeignKey)
    {found : ParentKey} (hold : catalog.parentKey position parent key = some found) (link : ForeignKeyLink)
    (same : link.key = key) : ∀ child ∈ childPositions link found, child ∈ key.columns := by
  have fromRowid : ∀ child ∈ childPositions link ParentKey.rowid, child ∈ key.columns := by
    intro child member
    simp only [childPositions, same] at member
    exact List.mem_of_mem_take member
  have fromColumns : ∀ pairs : List (Nat × Nat), (∀ pair ∈ pairs, pair.1 ∈ key.columns) →
      ∀ child ∈ childPositions link (ParentKey.columns pairs), child ∈ key.columns := by
    intro pairs good child member
    simp only [childPositions, List.mem_map] at member
    obtain ⟨pair, inPairs, rfl⟩ := member
    exact good pair inPairs
  unfold Catalog.parentKey at hold
  split at hold <;> try split at hold
  all_goals simp at hold
  all_goals (try split at hold)
  all_goals first
    | (cases hold; exact fromRowid)
    | (obtain ⟨pairs, rfl, good⟩ := primaryKey_children _ _ hold; exact fromColumns pairs good)
    | (obtain ⟨pairs, rfl, good⟩ := namedKey_children _ _ _ hold; exact fromColumns pairs good)

/-- For every catalog, position of an object, name that is not the name of that object and found object: the
object that the name finds is not at the position. Proof sketch: the found object has the folded name
({name}`findPosition_spec`), and the object at the position does not. -/
theorem Catalog.find_ne_position {catalog : Catalog} {position : Nat} {object : CatalogObject}
    (at_position : catalog[position]? = some object) {name : Identifier} (other : name.sameName object.name = false)
    {slot : Nat} {found : CatalogObject} (hold : catalog.find name = some (slot, found)) : slot ≠ position := by
  intro same
  subst same
  obtain ⟨same_object, named⟩ := findPosition_spec _ catalog hold
  cases Option.some.inj (same_object.symm.trans at_position)
  simp only [Bool.and_eq_true] at named
  rw [Identifier.sameName_comm] at other
  simp [named.1] at other

/-- For every catalog, position of an object, foreign key whose parent name is not the name of that object, and
parent that the key finds: the parent table or view is not at the position. Proof sketch:
{name}`Catalog.find_ne_position` for the first object of the name. -/
theorem Catalog.parentLink_position_ne {catalog : Catalog} {position : Nat} {object : CatalogObject}
    (at_position : catalog[position]? = some object) (key : ForeignKey) (other : key.table.sameName object.name = false)
    {place : Nat} (found : (∃ parentKey, catalog.parentLink key = .located place parentKey) ∨
      catalog.parentLink key = .mismatch place) : place ≠ position := by
  unfold Catalog.parentLink Catalog.findTable Catalog.findView at found
  rcases hold : catalog.find key.table with _ | ⟨slot, entry⟩
  · simp [hold] at found
  · have different := Catalog.find_ne_position at_position other hold
    rcases entry with ⟨name, kind⟩
    cases kind <;> simp only [hold] at found
    · rcases found with ⟨parentKey, found⟩ | found
      all_goals
        split at found <;> first | contradiction | (injection found with same; try (obtain ⟨rfl⟩ := same); simp_all)
    · rcases found with ⟨_, link⟩ | link <;> cases link
      exact different
    · rcases found with ⟨_, link⟩ | link <;> cases link
    · rcases found with ⟨_, link⟩ | link <;> cases link

/-- For every catalog, foreign key and parent key that the key finds in a table: each child position that the parent
key selects for a link of the key is a column of the key. Proof sketch: the link is located only by
{name}`Catalog.parentKey`, and {name}`Catalog.parentKey_children`. -/
theorem Catalog.parentLink_children (catalog : Catalog) (key : ForeignKey) {place : Nat} {found : ParentKey}
    (hold : catalog.parentLink key = .located place found) (link : ForeignKeyLink) (same : link.key = key) :
    ∀ child ∈ childPositions link found, child ∈ key.columns := by
  unfold Catalog.parentLink at hold
  cases table : catalog.findTable key.table with
  | none =>
    cases view : catalog.findView key.table <;> simp [table, view] at hold
  | some entry =>
    cases parentKey : catalog.parentKey entry.1 entry.2 key with
    | none => simp [table, parentKey] at hold
    | some chosen =>
      simp only [table, parentKey, ParentLink.located.injEq] at hold
      obtain ⟨_, rfl⟩ := hold
      exact Catalog.parentKey_children catalog entry.1 entry.2 key parentKey link same

end Belay.Sqlite.Model
