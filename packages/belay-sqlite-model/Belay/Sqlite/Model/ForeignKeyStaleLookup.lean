import Belay.Sqlite.Model.ForeignKeyRowAgreement
import Belay.Sqlite.Model.ForeignKeyRowPermutation
import Belay.Sqlite.Model.ForeignKeyCounterNew
import Belay.Sqlite.Model.ForeignKeySelfLookup
import Belay.Sqlite.Model.ForeignKeyLookupAppend

set_option doc.verso true

/-! Soundness conditions for UPDATE's retained old record and self-parent scans. -/

namespace Belay.Sqlite.Model

/-- For every lookup and new row, if every supplied stale row agrees with the new row
on the parent key, a successful stale lookup implies a successful lookup of the new singleton.
Proof sketch: transfer the successful stale witness through its key equality. -/
theorem parentFound_stale_rows (parent : CatalogTable) (key : ParentKey) (link : ForeignKeyLink)
    (values : List Value) (stale : List Row) (new : Row)
    (agrees : ∀ old ∈ stale, key.RowAgrees old new)
    (found : parentFound parent key link values stale none = true) :
    parentFound parent key link values [new] none = true := by
  rw [parentFound_any] at found
  obtain ⟨old, member, matched⟩ := List.any_eq_true.mp found
  rwa [parentFound_congr_parent_key (agrees old member)] at matched

/-- For every aligned present table, stored new row and link, a successful new-row
check implies reference satisfaction after append, provided any self shortcut is sound and
every stale self row agrees with the new parent key. Other parent positions need neither premise.
Proof sketch: current matches remain; self and stale matches transfer to the appended row. -/
theorem ForeignKeyLink.newRowSatisfied_append_stale {database : Database} {position : Nat} {parent : Table}
    (present : database.table position = some parent) (aligned : position < database.rows.length)
    (link : ForeignKeyLink) (new : Row) (stored : new.Stored parent.shape.columns)
    (stale : Option Row) (changed : List Nat)
    (selfSound : ∀ key, link.parent = .located position key → link.SelfLookupSound parent.shape key)
    (staleSound : ∀ key, link.parent = .located position key →
      ∀ old ∈ staleRows key stale changed, key.RowAgrees old new)
    (checked : newRowSatisfied database position new stale changed link = true) :
    link.satisfied (database.setRows position (parent.rows ++ [new])) new = true := by
  cases selected : link.parent with
  | missing => simpa [newRowSatisfied, ForeignKeyLink.satisfied, selected] using checked
  | mismatch other => simpa [newRowSatisfied, ForeignKeyLink.satisfied, selected] using checked
  | located other key =>
    by_cases self : other = position
    · subst other
      have atShape : database.catalog.tableAt position = some parent.shape := by
        obtain ⟨shape, atShape, same⟩ := Option.map_eq_some_iff.mp present
        subst parent
        exact atShape
      simp only [newRowSatisfied, selected, atShape, beq_self_eq_true, ite_true] at checked
      rw [parentFound_split_self, parentFound_append] at checked
      simp only [Bool.or_eq_true] at checked
      rw [ForeignKeyLink.satisfied_append_parent present aligned link key selected]
      rcases checked with null | self | old | previous
      · simp [ForeignKeyLink.satisfied, null]
      · simp [selfSound key selected new stored self]
      · simp [ForeignKeyLink.satisfied, selected, atShape, old]
      · simp [parentFound_stale_rows parent.shape key link new.values (staleRows key stale changed) new
          (staleSound key selected) previous]
    · rw [ForeignKeyLink.satisfied_setRows_other link database position _ new (by
        intro target targetKey equal
        rw [selected] at equal
        cases equal
        exact self)]
      cases atShape : database.catalog.tableAt other <;>
        simpa [newRowSatisfied, ForeignKeyLink.satisfied, selected, self, atShape] using checked

/-- For every parent key, old/new rows and changed positions, equal rowids and equal
cells outside the changed list imply that each retained stale row agrees with the new parent key.
Proof sketch: a column-key stale row is kept only when no selected parent column is marked changed. -/
theorem staleRows_agree (key : ParentKey) (old new : Row) (changed : List Nat)
    (rowid : old.rowid = new.rowid)
    (unchanged : ∀ position ∉ changed, old.values.getD position .null = new.values.getD position .null) :
    ∀ row ∈ staleRows key (some old) changed, key.RowAgrees row new := by
  cases key with
  | rowid =>
    intro row member
    simp only [staleRows, Option.toList_some, List.mem_singleton] at member
    subst row
    exact rowid
  | columns pairs =>
    simp only [staleRows]
    split
    · simp
    · rename_i noChange
      intro row member
      simp only [Option.toList_some, List.mem_singleton] at member
      subst row
      intro pair member
      apply unchanged
      have absent := List.any_eq_false.mp (Bool.eq_false_iff.mpr noChange) pair member
      simpa using absent

/-- For every parent-scan list with no link whose child is the updated table, supplying
a stale row gives the same decrement count as supplying none. Proof sketch: only self-table
scans append that row. An empty list needs no additional condition. -/
theorem parentDecrements_without_stale_self (database : Database) (position : Nat) (new : Row)
    (stale : Option Row) (parents : List ForeignKeyLink)
    (separate : ∀ link ∈ parents, link.child ≠ position) :
    parentDecrements database position new stale parents = parentDecrements database position new none parents := by
  unfold parentDecrements
  congr 1
  apply List.map_congr_left
  intro link member
  cases selected : link.parent with
  | missing | mismatch other => rfl
  | located other key => simp [separate link member]

/-- For every aligned present table with distinct rowids and member old row, a stored
replacement accepted by the new-row check after physical removal satisfies this link in the
in-place replacement. Any self shortcut must be sound; retained stale rows must agree on its
self-parent key. Other parent positions need neither premise. Proof sketch: append soundness
followed by the replacement permutation. -/
theorem ForeignKeyLink.newRowSatisfied_replace {database : Database} {position : Nat} {table : Table}
    (present : database.table position = some table) (aligned : position < database.rows.length)
    (distinct : table.RowidsDistinct) (old new : Row) (member : old ∈ table.rows)
    (newStored : new.Stored table.shape.columns) (link : ForeignKeyLink) (stale : Option Row) (changed : List Nat)
    (selfSound : ∀ key, link.parent = .located position key → link.SelfLookupSound table.shape key)
    (staleSound : ∀ key, link.parent = .located position key → ∀ previous ∈ staleRows key stale changed,
      key.RowAgrees previous new)
    (checked : newRowSatisfied (database.setRows position (table.rows.filter (·.rowid != old.rowid)))
      position new stale changed link = true) :
    link.satisfied (database.setRows position (LiteralData.replaceRow table old new).rows) new = true := by
  let remaining := table.rows.filter (·.rowid != old.rowid)
  let removed := database.setRows position remaining
  have atRemoved : removed.table position = some { table with rows := remaining } :=
    Database.table_setRows remaining present aligned
  have alignedRemoved : position < removed.rows.length := by simpa [removed, Database.setRows] using aligned
  have appended := link.newRowSatisfied_append_stale atRemoved alignedRemoved new newStored stale changed
    selfSound staleSound checked
  have replaced := database.rowsAt_setRows_perm present aligned (replaceRow_perm_append table.rows old new distinct member)
  have satisfiedPerm := ForeignKeyLink.satisfied_rows_perm
    (before := database.setRows position (LiteralData.replaceRow table old new).rows)
    (after := database.setRows position (remaining ++ [new])) rfl replaced link new
  rw [satisfiedPerm]
  simpa only [removed, Database.setRows, List.set_set] using appended

end Belay.Sqlite.Model
