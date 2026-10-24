import Belay.Sqlite.Model.ForeignKeyRowAgreement
import Belay.Sqlite.Model.ForeignKeyRowPermutation

set_option doc.verso true

/-! Exact reference and violation-count frames for replacements with unchanged key cells. -/

namespace Belay.Sqlite.Model

/-- For every parent lookup and row list with distinct rowids, replacing a member row
by a row with the same parent-key cells keeps the lookup result. Proof sketch: only the unique
old row changes, and its singleton match is unchanged. -/
theorem parentFound_replace_key (parent : CatalogTable) (key : ParentKey) (link : ForeignKeyLink)
    (values : List Value) (rows : List Row) (old new : Row) (distinct : (rows.map Row.rowid).Nodup)
    (member : old ∈ rows) (agrees : key.RowAgrees old new) :
    parentFound parent key link values rows none =
      parentFound parent key link values (rows.map fun row => if row.rowid == old.rowid then new else row) none := by
  rw [parentFound_any, parentFound_any, List.any_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  apply exists_congr
  intro row
  apply and_congr_right
  intro inside
  apply Bool.eq_iff_iff.mp
  dsimp only [Function.comp_def]
  split
  · rename_i equal
    have identity := Table.RowidsDistinct.row_eq (table := {shape := parent, rows}) distinct inside member (beq_iff_eq.mp equal)
    subst row
    exact parentFound_congr_parent_key agrees parent link values
  · rfl

/-- For every aligned present table with distinct rowids, replacing a member row keeps
this link's check on every fixed child row if the replacement agrees on its selected parent key.
A link to another position needs no key equality. Proof sketch: use unchanged-parent lookup
at the target and the existing row frame elsewhere. -/
theorem ForeignKeyLink.satisfied_replace_parent_frame {database : Database} {position : Nat} {table : Table}
    (present : database.table position = some table) (aligned : position < database.rows.length)
    (distinct : table.RowidsDistinct) (old new : Row) (member : old ∈ table.rows)
    (link : ForeignKeyLink) (row : Row)
    (agrees : ∀ key, link.parent = .located position key → key.RowAgrees old new) :
    link.satisfied database row =
      link.satisfied (database.setRows position (LiteralData.replaceRow table old new).rows) row := by
  cases selected : link.parent with
  | missing | mismatch other => simp [ForeignKeyLink.satisfied, selected]
  | located other key =>
    by_cases self : other = position
    · subst other
      have atShape : database.catalog.tableAt position = some table.shape := by
        obtain ⟨shape, atShape, equal⟩ := Option.map_eq_some_iff.mp present
        subst table
        exact atShape
      simp only [ForeignKeyLink.satisfied, selected,
        show (database.setRows position (LiteralData.replaceRow table old new).rows).catalog = database.catalog from rfl,
        atShape, Database.rowsAt, Database.table_setRows _ present aligned, present, Option.map_some, Option.getD_some]
      exact congrArg (link.hasNull row.values || ·)
        (parentFound_replace_key table.shape key link row.values table.rows old new distinct member (agrees key selected))
    · exact (ForeignKeyLink.satisfied_setRows_other link database position _ row (by
        intro target targetKey equal
        rw [selected] at equal
        cases equal
        exact self)).symm

/-- For every aligned present table with distinct rowids, replacing a member row keeps
the total violation count when all its child projections and all referencing parent keys agree.
No storedness, uniqueness or scan-comparison premise is needed. Proof sketch: every fixed
child's parent lookup is unchanged, and the replaced child's projection is unchanged too. -/
theorem Database.foreignKeyViolations_replace_unchanged {database : Database} {position : Nat} {table : Table}
    (present : database.table position = some table) (aligned : position < database.rows.length)
    (distinct : table.RowidsDistinct) (old new : Row) (member : old ∈ table.rows)
    (childAgrees : ∀ link ∈ childLinks database.catalog.foreignKeyLinks position, link.ChildAgrees old new)
    (parentAgrees : ∀ link ∈ database.catalog.foreignKeyLinks, ∀ key,
      link.parent = .located position key → key.RowAgrees old new) :
    (database.setRows position (LiteralData.replaceRow table old new).rows).foreignKeyViolations =
      database.foreignKeyViolations := by
  let after := database.setRows position (LiteralData.replaceRow table old new).rows
  unfold Database.foreignKeyViolations
  apply congrArg List.sum
  apply List.map_congr_left
  intro link inside
  have unchanged := fun row => ForeignKeyLink.satisfied_replace_parent_frame present aligned distinct old new member
    link row (parentAgrees link inside)
  have same : (fun row => !link.satisfied after row) = (fun row => !link.satisfied database row) := by
    funext row
    rw [unchanged row]
  change (after.rowsAt link.child).countP _ = _
  rw [same]
  by_cases self : link.child = position
  · rw [self]
    have childInside : link ∈ childLinks database.catalog.foreignKeyLinks position := by
      simp only [childLinks, List.mem_reverse, List.mem_filter, self, beq_self_eq_true, and_true]
      exact inside
    simp only [after, Database.rowsAt, Database.table_setRows _ present aligned, present,
      Option.map_some, Option.getD_some, LiteralData.replaceRow, List.countP_map]
    apply List.countP_congr
    intro row inRows
    dsimp only [Function.comp_def]
    split
    · rename_i equal
      have identity := distinct.row_eq inRows member (beq_iff_eq.mp equal)
      subst row
      rw [(childAgrees link childInside).satisfied database]
    · rfl
  · simp only [after, Database.rowsAt, Database.table_setRows_other database _ self]

end Belay.Sqlite.Model
