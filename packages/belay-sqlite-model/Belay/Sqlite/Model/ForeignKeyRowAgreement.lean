import Belay.Sqlite.Model.ForeignKeyParentUnique

set_option doc.verso true

/-! Equality of the child and parent cells that foreign-key comparisons read. -/

namespace Belay.Sqlite.Model

/-- Two rows agree on the cells read by a parent key: equal rowids for a rowid key,
or equal values at every selected parent column for a column key. Other cells are unrestricted.
Use this local fact when an UPDATE leaves a parent key unchanged. -/
def ParentKey.RowAgrees (key : ParentKey) (old new : Row) : Prop :=
  match key with
  | .rowid => old.rowid = new.rowid
  | .columns pairs => ∀ pair ∈ pairs, old.values.getD pair.2 .null = new.values.getD pair.2 .null

/-- For every parent definition, link and child values, two rows that agree on the
selected parent key give equal singleton lookup results. Proof sketch: each comparison reads
only the agreed rowid or selected columns. -/
theorem parentFound_congr_parent_key {key : ParentKey} {old new : Row}
    (agrees : key.RowAgrees old new) (parent : CatalogTable) (link : ForeignKeyLink) (values : List Value) :
    parentFound parent key link values [old] none = parentFound parent key link values [new] none := by
  cases key with
  | rowid =>
    simp only [ParentKey.RowAgrees] at agrees
    simp only [Belay.Sqlite.Model.parentFound]
    split <;> simp [agrees]
  | columns pairs =>
    simp only [Belay.Sqlite.Model.parentFound, Option.any_none, Bool.false_or, List.any_cons, List.any_nil, Bool.or_false]
    rw [indexHolds_childValues, indexHolds_childValues]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    apply forall_congr'
    intro pair
    apply imp_congr_right
    intro member
    rw [agrees pair member]

/-- For every lookup, equal values at all selected child positions give equal results,
with arbitrary parent rows and self shortcut. Proof sketch: the selected child-value lists coincide. -/
theorem parentFound_congr_child_values (parent : CatalogTable) (key : ParentKey) (link : ForeignKeyLink)
    (values other : List Value) (rows : List Row) (itself : Option Row)
    (agrees : ∀ position ∈ childPositions link key, values.getD position .null = other.getD position .null) :
    parentFound parent key link values rows itself = parentFound parent key link other rows itself := by
  have same : childValues link key values = childValues link key other := by
    apply List.map_congr_left
    exact agrees
  simp only [parentFound, same]

/-- For every parent key, definition and selected-cell index, rows that agree on the
key give equal parent cells. Proof sketch: rowid equality or the selected column equality. -/
theorem parentCell_congr_parent_key {key : ParentKey} {old new : Row} (agrees : key.RowAgrees old new)
    (parent : CatalogTable) (index : Nat) : parentCell parent key old index = parentCell parent key new index := by
  cases key with
  | rowid =>
    change old.rowid = new.rowid at agrees
    simp only [parentCell, agrees]
  | columns pairs =>
    cases pairAt : pairs[index]? with
    | none => simp [parentCell, pairAt]
    | some pair =>
      simp only [parentCell, pairAt, agrees pair (List.mem_of_getElem? pairAt)]

/-- For every child scan and fixed child row, parent rows that agree on the selected
key give equal matches. Proof sketch: all parent cells used by the scan are equal. -/
theorem childMatches_congr_parent_key {key : ParentKey} {old new : Row} (agrees : key.RowAgrees old new)
    (child parent : CatalogTable) (link : ForeignKeyLink) (row : Row) :
    childMatches child parent link key old row = childMatches child parent link key new row := by
  simp only [childMatches, parentCell_congr_parent_key agrees]

/-- Two rows have equal cells at every selected child position of this link. Located
parents use their comparison projection, including repeats; missing or mismatched parents use
the declaration columns. Other cells are unrestricted. Use this for an unchanged child key. -/
def ForeignKeyLink.ChildAgrees (link : ForeignKeyLink) (old new : Row) : Prop :=
  ∀ position ∈ (match link.parent with
    | .located _ key => childPositions link key
    | .missing | .mismatch _ => link.key.columns),
    old.values.getD position .null = new.values.getD position .null

/-- For every link and two rows agreeing on its child projection, their FK NULL tests
are equal. Proof sketch: the tests read the same selected values. -/
theorem ForeignKeyLink.ChildAgrees.hasNull {link : ForeignKeyLink} {old new : Row}
    (agrees : link.ChildAgrees old new) : link.hasNull old.values = link.hasNull new.values := by
  simp only [ForeignKeyLink.hasNull]
  cases selected : link.parent with
  | located position key =>
    have same : childValues link key old.values = childValues link key new.values := by
      apply List.map_congr_left
      simpa only [ForeignKeyLink.ChildAgrees, selected] using agrees
    simp only [same]
  | missing | mismatch position =>
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    apply exists_congr
    intro position
    apply and_congr_right
    intro member
    rw [agrees position (by simpa [selected] using member)]

/-- For every database, link and two rows agreeing on its child projection, their
reference checks are equal. Proof sketch: both the NULL test and parent lookup read that projection. -/
theorem ForeignKeyLink.ChildAgrees.satisfied {link : ForeignKeyLink} {old new : Row}
    (agrees : link.ChildAgrees old new) (database : Database) :
    link.satisfied database old = link.satisfied database new := by
  simp only [ForeignKeyLink.satisfied, agrees.hasNull]
  cases selected : link.parent with
  | missing | mismatch position => rfl
  | located position key =>
    have same : childValues link key old.values = childValues link key new.values := by
      apply List.map_congr_left
      simpa only [ForeignKeyLink.ChildAgrees, selected] using agrees
    cases shapeAt : database.catalog.tableAt position <;> simp [shapeAt, parentFound, same]

end Belay.Sqlite.Model
