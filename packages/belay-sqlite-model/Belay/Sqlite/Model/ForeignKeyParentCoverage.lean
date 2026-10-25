import Belay.Sqlite.Model.ForeignKeyMappingCoverage

set_option doc.verso true

/-! Parent-key selection connects UPDATE metadata to the cells that comparisons read. -/

namespace Belay.Sqlite.Model


/-- For every eligible index marked as the primary key, each column belongs to the
parent primary key. Proof sketch: only the synthesized primary index has this flag. -/
theorem Catalog.parentIndexes_primary_column {catalog : Catalog} {position : Nat} {parent : CatalogTable}
    {index : List (Nat × Collation)} (member : (true, index) ∈ catalog.parentIndexes position parent)
    {column : Nat × Collation} (inside : column ∈ index) : column.1 ∈ parent.primaryKey := by
  unfold Catalog.parentIndexes at member
  simp only [List.mem_append] at member
  rcases member with (primary | unique) | created
  · split at primary
    · simp at primary
    · simp only [List.mem_singleton, Prod.mk.injEq, true_and] at primary
      subst index
      obtain ⟨selected, selectedMember, equal⟩ := List.mem_map.mp inside
      subst column
      exact selectedMember
  · obtain ⟨key, _, equal⟩ := List.mem_map.mp unique
    cases equal
  · obtain ⟨object, _, selected⟩ := List.mem_filterMap.mp created
    cases kind : object.entry with
    | table table | view table => simp [kind] at selected
    | trigger trigger => simp [kind] at selected
    | index created =>
      simp only [kind] at selected
      split at selected
      · cases selected
      · obtain ⟨found, _, equal⟩ := Option.map_eq_some_iff.mp selected
        cases equal

/-- For every selected column pair, a false parent-change check means its parent column
is absent or unmarked. Proof sketch: implicit keys read the primary positions; explicit
keys read names that {name}`matchIndex_parent_unchanged` proves unmarked. -/
theorem Catalog.parentKey_columns_unchanged {catalog : Catalog} {position : Nat} {parent : CatalogTable}
    {key : ForeignKey} {pairs : List (Nat × Nat)}
    (found : catalog.parentKey position parent key = some (.columns pairs))
    {pair : Nat × Nat} (member : pair ∈ pairs) {changed : List Nat}
    (unchanged : key.parentChanged parent changed = false) :
    parent.columns[pair.2]? = none ∨ pair.2 ∉ changed := by
  unfold Catalog.parentKey at found
  extract_lets aliasNamed indexes at found
  split at found
  · cases found
  · split at found
    · rename_i implicit
      cases chosen : indexes.find? (·.1) with
      | none => simp [chosen] at found
      | some item =>
        simp only [chosen, Option.bind_some] at found
        split at found
        · cases found
          have indexMember := List.mem_of_find?_eq_some chosen
          have primary := List.find?_some chosen
          have parentMember := (List.of_mem_zip member).2
          obtain ⟨column, columnMember, equal⟩ := List.mem_map.mp parentMember
          have declared : column.1 ∈ parent.primaryKey := by
            apply Catalog.parentIndexes_primary_column (catalog := catalog) (position := position) (parent := parent)
              (index := item.2) (column := column) _ columnMember
            have same : (true, item.2) = item := by cases item; simp_all
            simpa only [same] using indexMember
          cases columnAt : parent.columns[pair.2]? with
          | none => exact .inl rfl
          | some column =>
            apply Or.inr
            intro written
            have ignored := List.any_eq_false.mp unchanged pair.2 written
            simp only [columnAt, implicit, ite_true] at ignored
            apply ignored
            simpa only [List.contains_iff_mem, equal] using declared
        · cases found
    · obtain ⟨selected, matched, equal⟩ := Option.map_eq_some_iff.mp found
      cases equal
      obtain ⟨index, _, matchFound⟩ := List.exists_of_findSome?_eq_some matched
      exact .inr (matchIndex_parent_unchanged matchFound member unchanged)

/-- For every selected rowid parent key, the table has an alias and the declaration
either omits parent names or names that alias alone. Proof sketch: this is the rowid
branch of {name}`Catalog.parentKey`; index branches return column keys. -/
theorem Catalog.parentKey_rowid_named {catalog : Catalog} {position : Nat} {parent : CatalogTable} {key : ForeignKey}
    (found : catalog.parentKey position parent key = some .rowid) :
    (match parent.rowidAlias, key.referenced with
    | some _, [] => true
    | some alias, [name] => (parent.columns[alias]?).any (·.name.sameName name)
    | some _, _ :: _ :: _ | none, _ => false) = true := by
  unfold Catalog.parentKey at found
  extract_lets aliasNamed indexes at found
  split at found
  · rename_i chosen
    exact (Bool.and_eq_true_iff.mp chosen).2
  · split at found
    · cases selected : indexes.find? (·.1) with
      | none => simp [selected] at found
      | some item =>
        simp only [selected, Option.bind_some] at found
        split at found <;> cases found
    · obtain ⟨selected, _, equal⟩ := Option.map_eq_some_iff.mp found
      cases equal

/-- For every selected rowid key whose alias belongs to the primary key, a false
parent-change check gives an alias whose column is absent or unmarked. Proof sketch:
implicit names check the primary key; an explicit name checks the selected alias. -/
theorem Catalog.parentKey_rowid_unchanged {catalog : Catalog} {position : Nat} {parent : CatalogTable}
    {key : ForeignKey} (found : catalog.parentKey position parent key = some .rowid)
    (aliasPrimary : ∀ alias, parent.rowidAlias = some alias → alias ∈ parent.primaryKey)
    {changed : List Nat} (unchanged : key.parentChanged parent changed = false) :
    ∃ alias, parent.rowidAlias = some alias ∧ (parent.columns[alias]? = none ∨ alias ∉ changed) := by
  have named := Catalog.parentKey_rowid_named found
  cases aliasAt : parent.rowidAlias with
  | none => simp [aliasAt] at named
  | some alias =>
    refine ⟨alias, rfl, ?_⟩
    cases columnAt : parent.columns[alias]? with
    | none => exact .inl rfl
    | some column =>
      apply Or.inr
      intro written
      have ignored := List.any_eq_false.mp unchanged alias written
      cases names : key.referenced with
      | nil =>
        simp only [columnAt, names, List.isEmpty_nil, ite_true] at ignored
        exact ignored (List.contains_iff_mem.mpr (aliasPrimary alias aliasAt))
      | cons name rest =>
        cases rest with
        | nil =>
          have same : name.sameName column.name = true := by
            simp only [aliasAt, columnAt, names, Option.any_some, Identifier.sameName, beq_iff_eq] at named ⊢
            exact named.symm
          simp only [columnAt, names, List.isEmpty_cons, Bool.false_eq_true, ite_false,
            List.any_cons, List.any_nil, Bool.or_false] at ignored
          exact ignored same
        | cons second rest => simp [aliasAt, names] at named

/-- For every selected parent key, two aliased rows agree on it when the parent-change
check is false and unmarked or absent cells agree. Each alias must belong to the primary
key. Proof sketch: column keys use their selected cells; rowid keys use the alias cell. -/
theorem Catalog.parentKey_rowAgrees {catalog : Catalog} {position : Nat} {parent : CatalogTable}
    {key : ForeignKey} {selected : ParentKey} (found : catalog.parentKey position parent key = some selected)
    (aliasPrimary : ∀ alias, parent.rowidAlias = some alias → alias ∈ parent.primaryKey)
    {changed : List Nat} (unchanged : key.parentChanged parent changed = false)
    {old new : Row} (oldAliased : old.Aliased parent.rowidAlias) (newAliased : new.Aliased parent.rowidAlias)
    (coverage : ∀ cell, cell ∉ changed ∨ parent.columns[cell]? = none →
      old.values.getD cell .null = new.values.getD cell .null) : selected.RowAgrees old new := by
  cases selected with
  | rowid =>
    obtain ⟨alias, aliasAt, absent⟩ := Catalog.parentKey_rowid_unchanged found aliasPrimary unchanged
    have same := coverage alias absent.symm
    simp only [List.getD_eq_getElem?_getD, oldAliased alias aliasAt, newAliased alias aliasAt,
      Option.getD_some, Value.integer.injEq] at same
    exact same
  | columns pairs =>
    intro pair member
    exact coverage pair.2 (Catalog.parentKey_columns_unchanged found member unchanged).symm

end Belay.Sqlite.Model
