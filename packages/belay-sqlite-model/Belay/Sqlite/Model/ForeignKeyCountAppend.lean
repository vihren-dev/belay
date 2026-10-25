import Belay.Sqlite.Model.ForeignKeyLookupAppend

set_option doc.verso true

/-! Per-link violation counts when a fresh row is appended. -/

namespace Belay.Sqlite.Model

/-- If every matched list element satisfies the original predicate, the remaining
predicate count plus the matched count equals the original count. Proof sketch: list induction. -/
private theorem countP_subtract_matches {α : Type} (rows : List α) (before matched : α → Bool)
    (unresolved : ∀ row ∈ rows, matched row = true → before row = true) :
    rows.countP (fun row => before row && !matched row) + rows.countP matched = rows.countP before := by
  induction rows with
  | nil => rfl
  | cons row rest induction =>
    have first := unresolved row (by simp)
    have later := induction (fun other member => unresolved other (by simp [member]))
    cases b : before row <;> cases m : matched row <;> simp_all <;> omega

/-- For every aligned parent table and link to it, under storedness, comparison
consistency and enlarged-table uniqueness, the after-append violation count plus the
old children matched by the new parent equals the old violation count plus the new
row violation when this is also the child table. Proof sketch: old matched children
were exactly repaired violations; count the appended self-child separately. -/
theorem ForeignKeyLink.violationCount_append_parent {database : Database} {position : Nat} {parent child : Table}
    (present : database.table position = some parent) (aligned : position < database.rows.length)
    (link : ForeignKeyLink) (key : ParentKey) (located : link.parent = .located position key)
    (childAt : database.table link.child = some child) (childStored : child.RowsStored)
    (new : Row) (newStored : new.Stored parent.shape.columns)
    (consistent : link.LookupScanConsistent child.shape parent.shape key) (keys : List UniqueKey)
    (unique : ({parent with rows := parent.rows ++ [new]} : Table).KeysUnique keys)
    (distinct : ({parent with rows := parent.rows ++ [new]} : Table).RowidsDistinct)
    (selectedUnique : ∀ pairs, key = .columns pairs → UniqueKey.ofColumns parent.shape.columns (pairs.map Prod.snd) ∈ keys) :
    ((database.setRows position (parent.rows ++ [new])).rowsAt link.child).countP
        (fun row => !link.satisfied (database.setRows position (parent.rows ++ [new])) row) +
      (childRows database link key position new [] false).length =
      (database.rowsAt link.child).countP (fun row => !link.satisfied database row) +
      (if !link.satisfied (database.setRows position (parent.rows ++ [new])) new && link.child == position then 1 else 0) := by
  let after := database.setRows position (parent.rows ++ [new])
  have counted := countP_subtract_matches child.rows
    (fun row => !link.satisfied database row) (fun row => childMatches child.shape parent.shape link key new row)
    (fun row inside matched => by
      have unresolved := ForeignKeyLink.matching_new_parent_unsatisfied present link key located child.shape new row
        newStored (childStored row inside) consistent keys unique distinct selectedUnique matched
      simpa using unresolved)
  have comparisons : child.rows.countP (fun row => !link.satisfied after row) =
      child.rows.countP (fun row => !link.satisfied database row && !childMatches child.shape parent.shape link key new row) := by
    apply List.countP_congr
    intro row inside
    rw [ForeignKeyLink.unsatisfied_append_parent present aligned link key located child.shape new row newStored
      (childStored row inside) consistent]
  rw [← comparisons] at counted
  have atShape : database.catalog.tableAt position = some parent.shape := by
    obtain ⟨shape, atShape, same⟩ := Option.map_eq_some_iff.mp present
    subst parent
    exact atShape
  rw [childRows_countP childAt atShape]
  simp only [Bool.false_and, Bool.not_false, Bool.and_true]
  by_cases self : link.child = position
  · have equal : child = parent := Option.some.inj (childAt.symm.trans (self ▸ present))
    subst child
    simp only [self, beq_self_eq_true, Bool.and_true, Database.rowsAt, present,
      Database.table_setRows _ present aligned, Option.map_some, Option.getD_some,
      List.countP_append, List.countP_singleton]
    dsimp only [after] at counted
    omega
  · have other : after.rowsAt link.child = database.rowsAt link.child := by
      simp only [after, Database.rowsAt, database.table_setRows_other _ self]
    change (after.rowsAt link.child).countP _ + _ = _
    rw [other]
    have childDifferent : (link.child == position) = false := by simp [self]
    simpa only [Database.rowsAt, childAt, Option.map_some, Option.getD_some, childDifferent,
      Bool.and_false, Bool.false_eq_true, ite_false, Nat.add_zero, after] using counted

/-- For every aligned table and link whose located parent is elsewhere, append adds
exactly the new row violation when the changed table is the child table, and otherwise
leaves the violation count unchanged. Missing and mismatched parents also satisfy this law.
Proof sketch: the parent lookup is unchanged; only a child-table append adds a row. -/
theorem ForeignKeyLink.violationCount_append_other {database : Database} {position : Nat} {table : Table}
    (present : database.table position = some table) (aligned : position < database.rows.length)
    (new : Row) (link : ForeignKeyLink)
    (untouched : ∀ parent key, link.parent = .located parent key → parent ≠ position) :
    ((database.setRows position (table.rows ++ [new])).rowsAt link.child).countP
        (fun row => !link.satisfied (database.setRows position (table.rows ++ [new])) row) =
      (database.rowsAt link.child).countP (fun row => !link.satisfied database row) +
      (if !link.satisfied (database.setRows position (table.rows ++ [new])) new && link.child == position then 1 else 0) := by
  have comparisons : (fun row => !link.satisfied (database.setRows position (table.rows ++ [new])) row) =
      (fun row => !link.satisfied database row) := by
    funext row
    rw [ForeignKeyLink.satisfied_setRows_other link database position _ row untouched]
  rw [comparisons]
  by_cases child : link.child = position
  · simp only [child, beq_self_eq_true, Bool.and_true, Database.rowsAt,
      Database.table_setRows _ present aligned, present, Option.map_some, Option.getD_some,
      List.countP_append, List.countP_singleton]
    rw [ForeignKeyLink.satisfied_setRows_other link database position _ new untouched]
  · have other : (database.setRows position (table.rows ++ [new])).rowsAt link.child = database.rowsAt link.child := by
      simp only [Database.rowsAt, database.table_setRows_other _ child]
    simp [other, child]

end Belay.Sqlite.Model
