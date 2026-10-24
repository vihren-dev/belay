import Belay.Sqlite.Model.ForeignKeyCountAppend

set_option doc.verso true

/-! The database-wide violation equation for physical row insertion. -/

namespace Belay.Sqlite.Model

/-- The number of old child rows repaired by this parent insertion for a link
located at the changed position. Other parent positions and missing/mismatched mappings
contribute zero. The count uses the existing engine scan without a stale row. -/
def parentInsertionMatches (database : Database) (position : Nat) (new : Row) (link : ForeignKeyLink) : Nat :=
  match link.parent with
  | .located parent key => if parent = position then (childRows database link key position new [] false).length else 0
  | .missing | .mismatch _ => 0

/-- If each list element satisfies its count equation, summing those equations
gives the total equation with one added unit for each true predicate. Proof sketch: list induction. -/
private theorem sum_delta_eq {α : Type} (xs : List α) (left right added : α → Nat) (predicate : α → Bool)
    (each : ∀ x ∈ xs, left x + added x = right x + (if predicate x then 1 else 0)) :
    (xs.map left).sum + (xs.map added).sum = (xs.map right).sum + xs.countP predicate := by
  induction xs with
  | nil => simp
  | cons x xs induction =>
    have first := each x (by simp)
    have rest := induction (fun x member => each x (by simp [member]))
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    cases test : predicate x <;> simp [test] at first ⊢ <;> omega

/-- For every aligned present table and stored new row, assume all stored rows,
uniqueness of the enlarged table, and lookup/scan consistency for every link targeting it.
Each selected column mapping must name an ordinary unique key of that table. Then the
after-append violation total plus repaired old-child counts equals the old total plus
violations of the appended row. Self-references are included. Proof sketch: apply the
per-link equations and sum over all declared links. -/
theorem Database.foreignKeyViolations_append_parent {database : Database} {position : Nat} {parent : Table}
    (present : database.table position = some parent) (aligned : position < database.rows.length)
    (stored : database.RowsStored) (new : Row) (newStored : new.Stored parent.shape.columns)
    (unique : ({parent with rows := parent.rows ++ [new]} : Table).KeysUnique (database.catalog.uniqueKeys position parent.shape))
    (distinct : ({parent with rows := parent.rows ++ [new]} : Table).RowidsDistinct)
    (consistent : ∀ link ∈ database.catalog.foreignKeyLinks, ∀ key child,
      link.parent = .located position key → database.table link.child = some child →
      link.LookupScanConsistent child.shape parent.shape key)
    (selectedUnique : ∀ link ∈ database.catalog.foreignKeyLinks, ∀ pairs,
      link.parent = .located position (.columns pairs) →
      UniqueKey.ofColumns parent.shape.columns (pairs.map Prod.snd) ∈ database.catalog.uniqueKeys position parent.shape) :
    (database.setRows position (parent.rows ++ [new])).foreignKeyViolations +
      (database.catalog.foreignKeyLinks.map (parentInsertionMatches database position new)).sum =
      database.foreignKeyViolations +
      (childLinks database.catalog.foreignKeyLinks position).countP
        (fun link => !link.satisfied (database.setRows position (parent.rows ++ [new])) new) := by
  let after := database.setRows position (parent.rows ++ [new])
  have each : ∀ link ∈ database.catalog.foreignKeyLinks,
      (after.rowsAt link.child).countP (fun row => !link.satisfied after row) +
        parentInsertionMatches database position new link =
      (database.rowsAt link.child).countP (fun row => !link.satisfied database row) +
        (if !link.satisfied after new && link.child == position then 1 else 0) := by
    intro link inside
    by_cases located : ∃ key, link.parent = .located position key
    · obtain ⟨key, selected⟩ := located
      have childMember : link ∈ childLinks database.catalog.foreignKeyLinks link.child := by
        simp only [childLinks, List.mem_reverse, List.mem_filter, beq_self_eq_true, and_true]
        exact inside
      obtain ⟨_, _, shape, atShape, _⟩ := (database.catalog.mem_childLinks_iff _ _).mp childMember
      let child : Table := {shape, rows := database.rows.getD link.child []}
      have childAt : database.table link.child = some child := by simp only [Database.table, atShape, Option.map_some, child]
      have count := ForeignKeyLink.violationCount_append_parent present aligned link key selected childAt
        (stored link.child child childAt) new newStored (consistent link inside key child selected childAt)
        (database.catalog.uniqueKeys position parent.shape) unique distinct
        (fun pairs same => selectedUnique link inside pairs (same ▸ selected))
      simpa only [parentInsertionMatches, selected, ite_true, after] using count
    · have untouched : ∀ other key, link.parent = .located other key → other ≠ position := by
        intro other key selected equal
        subst other
        exact located ⟨key, selected⟩
      have count := ForeignKeyLink.violationCount_append_other present aligned new link untouched
      have zero : parentInsertionMatches database position new link = 0 := by
        unfold parentInsertionMatches
        cases selected : link.parent with
        | missing => rfl
        | mismatch other => rfl
        | located other key => simp [untouched other key selected]
      simpa only [zero, Nat.add_zero, after] using count
  have count := sum_delta_eq database.catalog.foreignKeyLinks
    (fun link => (after.rowsAt link.child).countP (fun row => !link.satisfied after row))
    (fun link => (database.rowsAt link.child).countP (fun row => !link.satisfied database row))
    (parentInsertionMatches database position new)
    (fun link => !link.satisfied after new && link.child == position) each
  simpa only [Database.foreignKeyViolations, childLinks, List.countP_reverse,
    List.countP_filter, after, Database.setRows] using count

end Belay.Sqlite.Model
