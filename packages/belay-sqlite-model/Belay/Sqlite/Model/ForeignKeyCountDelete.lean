import Belay.Sqlite.Model.ForeignKeyCountRemoval
import Belay.Sqlite.Model.ForeignKeyCounterScans
import Belay.Sqlite.Model.ForeignKeyCounterRun

set_option doc.verso true

/-! The global counter bound across old-row checks and physical deletion, including self-references. -/

namespace Belay.Sqlite.Model

/-- Count the old row's matching children for a link whose located parent is the deletion
target, excluding its self-row. Other links contribute zero. This puts one parent-scan
contribution beside each catalog link for summation. -/
def parentRemovalMatches (database : Database) (position : Nat) (old : Row) (link : ForeignKeyLink) : Nat :=
  match link.parent with
  | .located parent key => if parent = position then (childRows database link key position old [] true).length else 0
  | .missing | .mismatch _ => 0

/-- Summing per-item bounds adds their predicate counts and nonnegative increments. -/
private theorem sum_delta_le {α : Type} (xs : List α) (left right added : α → Nat) (predicate : α → Bool)
    (each : ∀ x ∈ xs, left x + (if predicate x then 1 else 0) ≤ right x + added x) :
    (xs.map left).sum + xs.countP predicate ≤ (xs.map right).sum + (xs.map added).sum := by
  induction xs with
  | nil => simp
  | cons x xs induction =>
    have first := each x (by simp)
    have rest := induction (fun x member => each x (by simp [member]))
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    cases test : predicate x <;> simp [test] at first ⊢ <;> omega

/-- For every present old row, physical deletion increases the total violation count by
at most the matching parent-scan count, less its own unsatisfied child-link count. Rows are
aligned, the target has distinct rowids, every table stores its values, and every link to the
target has consistent lookup/scan comparisons. Proof sketch: sum the per-link deletion bounds;
catalog link membership supplies each child table, including self-references. -/
theorem Database.foreignKeyViolations_remove_parent {database : Database} {position : Nat} {parent : Table}
    (present : database.table position = some parent) (aligned : position < database.rows.length)
    (distinct : parent.RowidsDistinct) (stored : database.RowsStored)
    (old : Row) (member : old ∈ parent.rows)
    (consistent : ∀ link ∈ database.catalog.foreignKeyLinks, ∀ key child,
      link.parent = .located position key → database.table link.child = some child →
      link.LookupScanConsistent child.shape parent.shape key) :
    (database.setRows position (parent.rows.filter (·.rowid != old.rowid))).foreignKeyViolations +
      (childLinks database.catalog.foreignKeyLinks position).countP (fun link => !link.satisfied database old) ≤
      database.foreignKeyViolations +
      (database.catalog.foreignKeyLinks.map (parentRemovalMatches database position old)).sum := by
  let after := database.setRows position (parent.rows.filter (·.rowid != old.rowid))
  have each : ∀ link ∈ database.catalog.foreignKeyLinks,
      (after.rowsAt link.child).countP (fun row => !link.satisfied after row) +
        (if !link.satisfied database old && link.child == position then 1 else 0) ≤
      (database.rowsAt link.child).countP (fun row => !link.satisfied database row) +
        parentRemovalMatches database position old link := by
    intro link inside
    by_cases located : ∃ key, link.parent = .located position key
    · obtain ⟨key, selected⟩ := located
      have childMember : link ∈ childLinks database.catalog.foreignKeyLinks link.child := by
        simp only [childLinks, List.mem_reverse, List.mem_filter, beq_self_eq_true, and_true]
        exact inside
      obtain ⟨_, _, shape, atShape, _⟩ := (database.catalog.mem_childLinks_iff _ _).mp childMember
      let child : Table := {shape, rows := database.rows.getD link.child []}
      have childAt : database.table link.child = some child := by simp only [Database.table, atShape, Option.map_some, child]
      have bound := ForeignKeyLink.violationCount_remove_parent present aligned distinct (stored position parent present)
        old member link key selected childAt (stored link.child child childAt) (consistent link inside key child selected childAt)
      simpa only [parentRemovalMatches, selected, ite_true, after] using bound
    · have untouched : ∀ other key, link.parent = .located other key → other ≠ position := by
        intro other key selected equal
        subst other
        exact located ⟨key, selected⟩
      have bound := ForeignKeyLink.violationCount_remove_other present aligned old member link untouched
      have zero : parentRemovalMatches database position old link = 0 := by
        unfold parentRemovalMatches
        cases selected : link.parent with
        | missing => rfl
        | mismatch other => rfl
        | located other key => simp [untouched other key selected]
      simpa only [zero, Nat.add_zero, after] using bound
  have bound := sum_delta_le database.catalog.foreignKeyLinks
    (fun link => (after.rowsAt link.child).countP (fun row => !link.satisfied after row))
    (fun link => (database.rowsAt link.child).countP (fun row => !link.satisfied database row))
    (parentRemovalMatches database position old)
    (fun link => !link.satisfied database old && link.child == position) each
  simpa only [Database.foreignKeyViolations, childLinks, List.countP_reverse,
    List.countP_filter, after, Database.setRows] using bound

/-- For every database and link list, the sum of deletion scan contributions equals the
old-row increment of its selected parent links. Missing links contribute zero; incompatible
links are retained by selection but also contribute zero. Proof sketch: filtering and
reversing the list preserve the sum of the nonzero located-target contributions. -/
theorem parentRemovalMatches_sum (database : Database) (position : Nat) (old : Row) (links : List ForeignKeyLink) :
    (links.map (parentRemovalMatches database position old)).sum =
      parentIncrements database position old (parentLinks links position) := by
  simp only [parentIncrements, parentLinks, List.map_reverse, List.sum_reverse]
  induction links with
  | nil => rfl
  | cons link rest induction =>
    cases selected : link.parent with
    | missing => simpa [parentRemovalMatches, selected] using induction
    | mismatch other =>
      by_cases same : other = position <;> simpa [parentRemovalMatches, selected, same] using induction
    | located other key =>
      by_cases same : other = position <;> simp [parentRemovalMatches, selected, same, induction]

/-- For every state with the global counter bound, running its actual old-row checks and
then deleting a present row preserves that bound on success. A stop satisfies the stop-bound
predicate. Rows are aligned, the target has distinct rowids, all rows are stored, and every
link to the target has consistent lookup/scan comparisons. The ignore flag is unrestricted.
Proof sketch: old-row checks preserve rows and provide the required counter delta; the
physical deletion bound accounts for all child links and parent scans. An old-row stop is
undescribed and publishes no new rows. This phase law does not include later actions or triggers. -/
theorem oldSteps_remove_parent_counterBound {catalog : Catalog} {state : KeyState} {position : Nat} {table : Table}
    (bound : state.CounterBound catalog) (present : (state.database catalog).table position = some table)
    (aligned : position < state.rows.length) (distinct : table.RowidsDistinct)
    (stored : (state.database catalog).RowsStored) (old : Row) (member : old ∈ table.rows)
    (consistent : ∀ link ∈ catalog.foreignKeyLinks, ∀ key child,
      link.parent = .located position key → (state.database catalog).table link.child = some child →
      link.LookupScanConsistent child.shape table.shape key) (ignore : Bool) :
    ResultHolds (KeyState.CounterBound catalog) (KeyStop.CounterBound catalog)
      ((fun reached => reached.changeRows position (fun rows => rows.filter (·.rowid != old.rowid))) <$>
        oldSteps catalog state position old (childLinks catalog.foreignKeyLinks position)
          (parentLinks catalog.foreignKeyLinks position) ignore) := by
  have removed := Database.foreignKeyViolations_remove_parent present aligned distinct stored old member consistent
  rw [parentRemovalMatches_sum] at removed
  have lower := oldSteps_counter_delta catalog state position old
    (childLinks catalog.foreignKeyLinks position) (parentLinks catalog.foreignKeyLinks position) ignore
  have kept := oldSteps_rows catalog state position old
    (childLinks catalog.foreignKeyLinks position) (parentLinks catalog.foreignKeyLinks position) ignore
  have tableRows : table.rows = state.rows.getD position [] := by
    obtain ⟨shape, _, equal⟩ := Option.map_eq_some_iff.mp present
    subst table
    rfl
  cases result : oldSteps catalog state position old
      (childLinks catalog.foreignKeyLinks position) (parentLinks catalog.foreignKeyLinks position) ignore with
  | error stop =>
    rw [result] at kept
    dsimp only [ResultHolds] at kept
    subst stop
    trivial
  | ok reached =>
    rw [result] at kept lower
    dsimp only [ResultHolds] at kept lower
    change (reached.changeRows position (fun rows => rows.filter (·.rowid != old.rowid))).CounterBound catalog
    have same : (reached.changeRows position (fun rows => rows.filter (·.rowid != old.rowid))).database catalog =
        (state.database catalog).setRows position (table.rows.filter (·.rowid != old.rowid)) := by
      simp only [KeyState.changeRows, KeyState.database, Database.setRows, kept, tableRows]
    unfold KeyState.CounterBound
    rw [same]
    change ((_ : Nat) : Int) ≤ reached.counter
    unfold KeyState.CounterBound at bound
    dsimp only [KeyState.database] at removed lower bound ⊢
    omega

end Belay.Sqlite.Model
