import Belay.Sqlite.Model.ForeignKeyCountRows

set_option doc.verso true

/-! Per-link violation bounds for deleting a parent or an unrelated row. -/

namespace Belay.Sqlite.Model

/-- A predicate count is bounded by two other counts when every counted member satisfies
at least one of their predicates. -/
private theorem countP_le_two {α : Type} (rows : List α) (after before added : α → Bool)
    (covered : ∀ row ∈ rows, after row = true → before row = true ∨ added row = true) :
    rows.countP after ≤ rows.countP before + rows.countP added := by
  induction rows with
  | nil => simp
  | cons row rest induction =>
    have first := covered row (by simp)
    have later := induction (fun other member => covered other (by simp [member]))
    cases hAfter : after row <;> cases hBefore : before row <;> cases hAdded : added row <;>
      simp_all <;> omega

/-- For every located link, deleting a present parent row produces at most the original
violation count plus its child-scan count, less the old row's violation when it is also a child.
Rows are aligned, parent rowids are distinct, both tables store their values, and lookup/scan
comparisons agree for all stored pairs. This includes self-references. Proof sketch: every
new violation has a removed-parent scan witness; deleting the self-row removes its old
violation and excludes it from the scan. -/
theorem ForeignKeyLink.violationCount_remove_parent {database : Database} {position : Nat} {parent child : Table}
    (present : database.table position = some parent) (aligned : position < database.rows.length)
    (distinct : parent.RowidsDistinct) (stored : parent.RowsStored)
    (old : Row) (member : old ∈ parent.rows) (link : ForeignKeyLink) (key : ParentKey)
    (located : link.parent = .located position key) (childAt : database.table link.child = some child)
    (childStored : child.RowsStored) (consistent : link.LookupScanConsistent child.shape parent.shape key) :
    ((database.setRows position (parent.rows.filter (·.rowid != old.rowid))).rowsAt link.child).countP
        (fun row => !link.satisfied (database.setRows position (parent.rows.filter (·.rowid != old.rowid))) row) +
      (if !link.satisfied database old && link.child == position then 1 else 0) ≤
      (database.rowsAt link.child).countP (fun row => !link.satisfied database row) +
      (childRows database link key position old [] true).length := by
  let after := database.setRows position (parent.rows.filter (·.rowid != old.rowid))
  have atShape : database.catalog.tableAt position = some parent.shape := by
    obtain ⟨shape, atShape, same⟩ := Option.map_eq_some_iff.mp present
    subst parent
    exact atShape
  rw [childRows_countP childAt atShape]
  have covered (row : Row) (inside : row ∈ child.rows) (failed : (!link.satisfied after row) = true) :
      (!link.satisfied database row) = true ∨ childMatches child.shape parent.shape link key old row = true := by
    have out := ForeignKeyLink.unsatisfied_remove_parent present aligned distinct stored old member link key
      located child.shape row (childStored row inside) consistent (by simpa using failed)
    simpa using out
  by_cases self : link.child = position
  · have equal : child = parent := Option.some.inj (childAt.symm.trans (self ▸ present))
    subst child
    have bounds := countP_le_two (parent.rows.filter (·.rowid != old.rowid))
      (fun row => !link.satisfied after row) (fun row => !link.satisfied database row)
      (fun row => childMatches parent.shape parent.shape link key old row)
      (fun row inside => covered row (List.mem_filter.mp inside).1)
    have removed := countP_remove_rowid (fun row => !link.satisfied database row) parent.rows old member
    have scan : (parent.rows.filter (·.rowid != old.rowid)).countP
        (fun row => childMatches parent.shape parent.shape link key old row) =
        parent.rows.countP (fun row => childMatches parent.shape parent.shape link key old row &&
          !(true && link.child == position && row.rowid == old.rowid)) := by
      simp only [List.countP_filter, self, beq_self_eq_true, Bool.true_and]
      rfl
    rw [scan] at bounds
    dsimp only [after] at bounds
    simp only [self, beq_self_eq_true, Bool.true_and] at bounds
    simp only [self, beq_self_eq_true, Bool.and_true, Database.rowsAt, present,
      Database.table_setRows _ present aligned, Option.map_some, Option.getD_some, Bool.true_and]
    omega
  · have other : after.rowsAt link.child = database.rowsAt link.child := by
      simp only [after, Database.rowsAt, database.table_setRows_other _ self]
    change (after.rowsAt link.child).countP _ + _ ≤ _
    rw [other]
    have bounds := countP_le_two child.rows (fun row => !link.satisfied after row)
      (fun row => !link.satisfied database row) (fun row => childMatches child.shape parent.shape link key old row) covered
    have childDifferent : (link.child == position) = false := by simp [self]
    simpa only [Database.rowsAt, childAt, Option.map_some, Option.getD_some, childDifferent,
      Bool.and_false, Bool.false_and, Bool.not_false, Bool.and_true, Bool.false_eq_true,
      ite_false, Nat.add_zero, after] using bounds

/-- For every link whose located parent is not the deletion target, deleting a present row
creates no new violations and removes that row's violation when it is a child of the link.
Rows are aligned; duplicate rowids are allowed. Proof sketch: parent comparisons are unchanged,
and filtering child rows removes at least the old row's contribution. -/
theorem ForeignKeyLink.violationCount_remove_other {database : Database} {position : Nat} {table : Table}
    (present : database.table position = some table) (aligned : position < database.rows.length)
    (old : Row) (member : old ∈ table.rows) (link : ForeignKeyLink)
    (untouched : ∀ parent key, link.parent = .located parent key → parent ≠ position) :
    ((database.setRows position (table.rows.filter (·.rowid != old.rowid))).rowsAt link.child).countP
        (fun row => !link.satisfied (database.setRows position (table.rows.filter (·.rowid != old.rowid))) row) +
      (if !link.satisfied database old && link.child == position then 1 else 0) ≤
      (database.rowsAt link.child).countP (fun row => !link.satisfied database row) := by
  have comparisons : (fun row => !link.satisfied (database.setRows position (table.rows.filter (·.rowid != old.rowid))) row) =
      (fun row => !link.satisfied database row) := by
    funext row
    rw [ForeignKeyLink.satisfied_setRows_other link database position _ row untouched]
  rw [comparisons]
  by_cases child : link.child = position
  · simp only [child, beq_self_eq_true, Bool.and_true, Database.rowsAt,
      Database.table_setRows _ present aligned, present, Option.map_some, Option.getD_some]
    exact countP_remove_rowid _ table.rows old member
  · have other : (database.setRows position (table.rows.filter (·.rowid != old.rowid))).rowsAt link.child =
        database.rowsAt link.child := by
      simp only [Database.rowsAt, database.table_setRows_other _ child]
    simp [other, child]

end Belay.Sqlite.Model
