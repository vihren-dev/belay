import Belay.Sqlite.Model.ForeignKeyRowAgreement
import Belay.Sqlite.Model.Resolution.CatalogSpec

set_option doc.verso true

/-! Selected FK projections are covered by declaration-column change checks. -/

namespace Belay.Sqlite.Model


/-- Every member of a successful optional map comes from an input member. -/
private theorem mapM_some_mem {α β : Type} (f : α → Option β) : ∀ {items : List α} {values : List β},
    items.mapM f = some values → ∀ value ∈ values, ∃ item ∈ items, f item = some value := by
  intro items
  induction items with
  | nil => intro values result; simp only [List.mapM_nil, pure, Option.some.injEq] at result; subst values; simp
  | cons first rest induction =>
    intro values result value member
    simp only [List.mapM_cons, bind, Option.bind] at result
    cases head : f first with
    | none => simp [head] at result
    | some found =>
      cases tail : rest.mapM f with
      | none => simp [head, tail] at result
      | some later =>
        simp only [head, tail, pure, Option.some.injEq] at result
        subst values
        rcases List.mem_cons.mp member with same | inside
        · subst value; exact ⟨first, by simp, head⟩
        · obtain ⟨item, inside, mapped⟩ := induction tail value inside
          exact ⟨item, by simp [inside], mapped⟩

/-- For every successful explicit index mapping, each selected child position belongs to
the declaration. Repeated positions are retained. Proof sketch: each match selects one
declaration position through the referenced-name index. -/
theorem matchIndex_child_mem {parent : CatalogTable} {key : ForeignKey} {index : List (Nat × Collation)}
    {pairs : List (Nat × Nat)} (matched : matchIndex parent key index = some pairs) {pair : Nat × Nat}
    (member : pair ∈ pairs) : pair.1 ∈ key.columns := by
  unfold matchIndex at matched
  split at matched
  · cases matched
  · obtain ⟨⟨column, collation⟩, _, mapped⟩ := mapM_some_mem _ matched pair member
    dsimp only at mapped
    cases definition : parent.columns[column]? with
    | none => simp [definition] at mapped
    | some defined =>
      simp only [definition, bind, Option.bind] at mapped
      split at mapped
      · cases mapped
      · cases place : key.referenced.findIdx? (·.sameName defined.name) with
        | none => simp [place] at mapped
        | some position =>
          cases child : key.columns[position]? with
          | none => simp [place, child] at mapped
          | some childPosition =>
            simp only [place, child, pure, Option.some.injEq] at mapped
            subst pair
            exact List.mem_of_getElem? child

/-- For every successful explicit index mapping and selected pair, a false
{name}`ForeignKey.parentChanged` check means that the selected parent position is unmarked.
Proof sketch: the matching declaration name would otherwise make the check true. -/
theorem matchIndex_parent_unchanged {parent : CatalogTable} {key : ForeignKey} {index : List (Nat × Collation)}
    {pairs : List (Nat × Nat)} (matched : matchIndex parent key index = some pairs) {pair : Nat × Nat}
    (member : pair ∈ pairs) {changed : List Nat} (unchanged : key.parentChanged parent changed = false) :
    pair.2 ∉ changed := by
  unfold matchIndex at matched
  split at matched
  · cases matched
  · obtain ⟨⟨column, collation⟩, _, mapped⟩ := mapM_some_mem _ matched pair member
    dsimp only at mapped
    cases definition : parent.columns[column]? with
    | none => simp [definition] at mapped
    | some defined =>
      simp only [definition, bind, Option.bind] at mapped
      split at mapped
      · cases mapped
      · cases place : key.referenced.findIdx? (·.sameName defined.name) with
        | none => simp [place] at mapped
        | some position =>
          cases child : key.columns[position]? with
          | none => simp [place, child] at mapped
          | some childPosition =>
            simp only [place, child, pure, Option.some.injEq] at mapped
            subst pair
            intro changedHere
            have ignored := List.any_eq_false.mp unchanged column changedHere
            have nonempty : key.referenced.isEmpty = false := by
              cases names : key.referenced with
              | nil => simp [names] at place
              | cons first rest => rfl
            obtain ⟨below, named, _⟩ := List.findIdx?_eq_some_iff_getElem.mp place
            have found : key.referenced.any (·.sameName defined.name) = true := List.any_eq_true.mpr ⟨key.referenced[position], List.getElem_mem below, named⟩
            simp only [definition, nonempty, Bool.false_eq_true, ite_false] at ignored
            exact ignored found

/-- For every selected parent key and child position in its projection, the position
belongs to the foreign-key declaration. Proof sketch: rowid selection takes one declared
position; implicit keys zip declarations; explicit keys use {name}`matchIndex_child_mem`. -/
theorem Catalog.parentKey_child_mem {catalog : Catalog} {position : Nat} {parent : CatalogTable} {key : ForeignKey}
    {selected : ParentKey} (found : catalog.parentKey position parent key = some selected)
    {childPosition : Nat} (member : childPosition ∈ childPositions { child := 0, key, parent := .located position selected } selected) :
    childPosition ∈ key.columns := by
  unfold Catalog.parentKey at found
  extract_lets aliasNamed indexes at found
  split at found
  · cases found
    exact List.mem_of_mem_take member
  · split at found
    · rename_i implicit
      cases index : indexes.find? (·.1) with
      | none => simp [index] at found
      | some item =>
        simp only [index, Option.bind_some] at found
        split at found
        · cases found
          obtain ⟨pair, paired, same⟩ := List.mem_map.mp member
          subst childPosition
          exact List.of_mem_zip paired |>.1
        · cases found
    · obtain ⟨pairs, matched, equal⟩ := Option.map_eq_some_iff.mp found
      subst selected
      obtain ⟨pair, paired, same⟩ := List.mem_map.mp member
      subst childPosition
      obtain ⟨index, _, matchFound⟩ := List.exists_of_findSome?_eq_some matched
      exact matchIndex_child_mem matchFound paired

/-- For every link with its catalog-selected located parent, each selected child target
belongs to its declaration. Missing and mismatched parents are outside this law.
Proof sketch: unpack parent selection and apply {name}`Catalog.parentKey_child_mem`. -/
theorem Catalog.parentLink_child_mem {catalog : Catalog} {link : ForeignKeyLink} {position : Nat} {selected : ParentKey}
    (choice : link.parent = catalog.parentLink link.key) (located : link.parent = .located position selected)
    {childPosition : Nat} (member : childPosition ∈ childPositions link selected) : childPosition ∈ link.key.columns := by
  rw [choice] at located
  unfold Catalog.parentLink at located
  split at located
  · split at located <;> cases located
  · rename_i parentPosition parent found
    split at located
    · rename_i key chosen
      cases located
      exact Catalog.parentKey_child_mem chosen member
    · cases located

/-- For every catalog-selected link and two rows, an unchanged declaration and equal
unmarked cells imply equal selected child cells. Missing or mismatched parents use the
declaration fallback. Proof sketch: every selected position belongs to the declaration. -/
theorem ForeignKeyLink.childAgrees_of_unchanged {catalog : Catalog} {link : ForeignKeyLink} {old new : Row}
    {changed : List Nat} (choice : link.parent = catalog.parentLink link.key)
    (unchanged : link.key.childChanged changed = false)
    (coverage : ∀ position ∉ changed, old.values.getD position .null = new.values.getD position .null) :
    link.ChildAgrees old new := by
  intro position member
  apply coverage
  have declared : position ∈ link.key.columns := by
    cases parent : link.parent with
    | missing | mismatch other => simpa [parent] using member
    | located other key => exact Catalog.parentLink_child_mem choice parent (by simpa [parent] using member)
  have notChanged := List.any_eq_false.mp unchanged position declared
  simpa using notChanged


end Belay.Sqlite.Model
