import Belay.Sqlite.Model.ForeignKeyParentCoverage

set_option doc.verso true

/-! The actual UPDATE link filters supply the omitted-check frame premises. -/

namespace Belay.Sqlite.Model

/-- For every table object and catalog-selected link located at that object, its
declaration references the object name. Proof sketch: the selected table lookup gives
folded-name equality. The link need not itself be a child of that table. -/
theorem Catalog.parentLink_selfReferences {catalog : Catalog} {link : ForeignKeyLink} {position : Nat}
    {name : Identifier} {table : CatalogTable} {key : ParentKey}
    (atTarget : catalog[position]? = some { name, entry := .table table })
    (choice : link.parent = catalog.parentLink link.key) (located : link.parent = .located position key) :
    link.key.selfReferences name = true := by
  rw [choice] at located
  unfold Catalog.parentLink at located
  split at located
  · split at located <;> cases located
  · rename_i parentPosition parent found
    split at located
    · cases located
      obtain ⟨object, atObject, _, sameName⟩ := Catalog.findTable_some catalog link.key.table position parent found
      rw [atTarget, Option.some.injEq] at atObject
      subst object
      simpa only [ForeignKey.selfReferences, Identifier.sameName, beq_iff_eq] using sameName.symm
    · cases located

/-- For every selected child link omitted by the actual UPDATE filter, unmarked-cell
equality gives child agreement and any self-parent agreement. The self-parent case is
impossible because the filter includes self references. Proof sketch: selected child
positions are declared, and a located self parent makes the self-reference check true. -/
theorem Catalog.updateChildren_unchanged {catalog : Catalog} {link : ForeignKeyLink} {position : Nat}
    {name : Identifier} {table : CatalogTable} {changed : List Nat} {old new : Row}
    (atTarget : catalog[position]? = some { name, entry := .table table })
    (member : link ∈ childLinks catalog.foreignKeyLinks position)
    (inactive : (link.key.childChanged changed || link.key.selfReferences name) = false)
    (coverage : ∀ cell ∉ changed, old.values.getD cell .null = new.values.getD cell .null) :
    link.ChildAgrees old new ∧ ∀ key, link.parent = .located position key → key.RowAgrees old new := by
  obtain ⟨_, selected, _⟩ := (catalog.mem_childLinks_iff position link).mp member
  have inactiveChild : link.key.childChanged changed = false := (Bool.or_eq_false_iff.mp inactive).1
  have inactiveSelf : link.key.selfReferences name = false := (Bool.or_eq_false_iff.mp inactive).2
  refine ⟨ForeignKeyLink.childAgrees_of_unchanged selected inactiveChild coverage, ?_⟩
  intro key located
  have self := Catalog.parentLink_selfReferences atTarget selected located
  rw [inactiveSelf] at self
  contradiction

/-- For every located catalog-selected parent link, its declared table was found at
that position and selected that parent key. Proof sketch: unpack the two successful
lookups in {name}`Catalog.parentLink`. -/
theorem Catalog.parentLink_located {catalog : Catalog} {foreign : ForeignKey} {position : Nat} {key : ParentKey}
    (selected : catalog.parentLink foreign = .located position key) :
    ∃ parent, catalog.findTable foreign.table = some (position, parent) ∧ catalog.parentKey position parent foreign = some key := by
  unfold Catalog.parentLink at selected
  split at selected
  · split at selected <;> cases selected
  · rename_i target parent found
    split at selected
    · rename_i comparison chosen
      cases selected
      exact ⟨parent, found, chosen⟩
    · cases selected

/-- For every catalog link to a present target, a false parent-change check gives key
agreement when both rows are aliased, aliases belong to the primary key, and unmarked or
absent cells agree. Other parent positions need nothing. Proof sketch: recover the
selected parent key and use {name}`Catalog.parentKey_rowAgrees`. -/
theorem Catalog.updateParents_unchanged {catalog : Catalog} {link : ForeignKeyLink} {position : Nat}
    {table : CatalogTable} {changed : List Nat} {old new : Row}
    (atTarget : catalog.tableAt position = some table)
    (member : link ∈ catalog.foreignKeyLinks)
    (inactive : link.key.parentChanged table changed = false)
    (aliasPrimary : ∀ alias, table.rowidAlias = some alias → alias ∈ table.primaryKey)
    (oldAliased : old.Aliased table.rowidAlias) (newAliased : new.Aliased table.rowidAlias)
    (coverage : ∀ cell, cell ∉ changed ∨ table.columns[cell]? = none →
      old.values.getD cell .null = new.values.getD cell .null) :
    ∀ key, link.parent = .located position key → key.RowAgrees old new := by
  intro key located
  have childMember : link ∈ childLinks catalog.foreignKeyLinks link.child := by
    simp only [childLinks, List.mem_reverse, List.mem_filter, beq_self_eq_true, and_true]
    exact member
  obtain ⟨_, selected, _⟩ := (catalog.mem_childLinks_iff link.child link).mp childMember
  rw [selected] at located
  obtain ⟨parent, found, chosen⟩ := Catalog.parentLink_located located
  obtain ⟨object, atObject, entry, _⟩ := Catalog.findTable_some catalog link.key.table position parent found
  have same : parent = table := by
    cases object with
    | mk name kind =>
      dsimp only at entry
      subst kind
      simpa only [Catalog.tableAt, atObject, Option.some.injEq] using atTarget
  subst parent
  exact Catalog.parentKey_rowAgrees chosen aliasPrimary inactive oldAliased newAliased coverage

/-- For every link list and UPDATE classified at level zero, all child-change checks
and all parent-change checks are false. Proof sketch: the level-zero branch requires
both filtered lists to be empty. -/
theorem updateLevel_zero_checks {links : List ForeignKeyLink} {position : Nat} {name : Identifier}
    {table : CatalogTable} {changed : List Nat} (zero : updateLevel links position name table changed = 0) :
    (∀ link ∈ childLinks links position, link.key.childChanged changed = false) ∧
    (∀ link ∈ parentLinks links position, link.key.parentChanged table changed = false) := by
  unfold updateLevel at zero
  extract_lets children parents at zero
  split at zero
  · cases zero
  · split at zero
    · rename_i empty
      have childEmpty : children = [] := List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp empty).1
      have parentEmpty : parents = [] := List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp empty).2
      constructor
      · simpa only [children, List.filter_eq_nil_iff, Bool.not_eq_true] using childEmpty
      · simpa only [parents, List.filter_eq_nil_iff, Bool.not_eq_true] using parentEmpty
    · cases zero

/-- For every present target and level-zero UPDATE, aliased rows with equal unmarked
or absent cells agree on every child projection and referencing parent key, when aliases
belong to the primary key. Proof sketch: level zero makes each declaration check false;
the catalog-selection laws give the cells actually read. This discharges the count frame
for UPDATEs that skip both check phases. -/
theorem Catalog.updateLevel_zero_agrees {catalog : Catalog} {position : Nat}
    {name : Identifier} {table : CatalogTable} {changed : List Nat} {old new : Row}
    (atTarget : catalog.tableAt position = some table)
    (zero : updateLevel catalog.foreignKeyLinks position name table changed = 0)
    (aliasPrimary : ∀ alias, table.rowidAlias = some alias → alias ∈ table.primaryKey)
    (oldAliased : old.Aliased table.rowidAlias) (newAliased : new.Aliased table.rowidAlias)
    (coverage : ∀ cell, cell ∉ changed ∨ table.columns[cell]? = none →
      old.values.getD cell .null = new.values.getD cell .null) :
    (∀ link ∈ childLinks catalog.foreignKeyLinks position, link.ChildAgrees old new) ∧
    (∀ link ∈ catalog.foreignKeyLinks, ∀ key,
      link.parent = .located position key → key.RowAgrees old new) := by
  have checks := updateLevel_zero_checks zero
  constructor
  · intro link member
    obtain ⟨_, selected, _⟩ := (catalog.mem_childLinks_iff position link).mp member
    exact ForeignKeyLink.childAgrees_of_unchanged selected (checks.1 link member)
      (fun cell absent => coverage cell (.inl absent))
  · intro link member key selected
    have parentMember : link ∈ parentLinks catalog.foreignKeyLinks position := by
      simp only [parentLinks, List.mem_reverse, List.mem_filter, member, true_and]
      simp [selected]
    exact Catalog.updateParents_unchanged atTarget member (checks.2 link parentMember)
      aliasPrimary oldAliased newAliased coverage key selected

end Belay.Sqlite.Model
