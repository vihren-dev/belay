import Belay.Sqlite.Model.ForeignKeySelfLookup
import Belay.Sqlite.Model.ForeignKeyCountInsert
import Belay.Sqlite.Model.ForeignKeyCounterNew

set_option doc.verso true

/-! The global counter bound through actual new-row checks and physical insertion. -/

namespace Belay.Sqlite.Model

/-- For every aligned present table, stored new row and link, if the self-parent
shortcut is sound whenever this table is its parent, a successful new-row check without
a stale row implies satisfaction after append. Other parent positions need no shortcut
premise. Proof sketch: existing parent matches remain, and accepted self matches become
ordinary matches in the appended singleton. -/
theorem ForeignKeyLink.newRowSatisfied_append {database : Database} {position : Nat} {parent : Table}
    (present : database.table position = some parent) (aligned : position < database.rows.length)
    (link : ForeignKeyLink) (new : Row) (stored : new.Stored parent.shape.columns)
    (selfSound : ∀ key, link.parent = .located position key → link.SelfLookupSound parent.shape key)
    (checked : newRowSatisfied database position new none [] link = true) :
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
      have staleEmpty : staleRows key none [] = [] := by cases key <;> simp [staleRows]
      simp only [staleEmpty, List.append_nil] at checked
      rw [parentFound_split_self] at checked
      simp only [Bool.or_eq_true] at checked
      rw [ForeignKeyLink.satisfied_append_parent present aligned link key selected]
      rcases checked with null | self | old
      · simp [ForeignKeyLink.satisfied, null]
      · simp [selfSound key selected new stored self]
      · simp [ForeignKeyLink.satisfied, selected, atShape, old]
    · rw [ForeignKeyLink.satisfied_setRows_other link database position _ new (by
        intro target targetKey equal
        rw [selected] at equal
        cases equal
        exact self)]
      cases atShape : database.catalog.tableAt other <;>
        simpa [newRowSatisfied, ForeignKeyLink.satisfied, selected, self, atShape] using checked

/-- For every link list, the total insertion match count equals
{name}`parentDecrements` over its selected parent links with no stale row.
Proof sketch: filter the list by the located parent position; other cases contribute zero. -/
theorem parentInsertionMatches_sum (database : Database) (position : Nat) (new : Row)
    (links : List ForeignKeyLink) :
    (links.map (parentInsertionMatches database position new)).sum =
      parentDecrements database position new none (parentLinks links position) := by
  simp only [parentDecrements, parentLinks, List.map_reverse, List.sum_reverse]
  induction links with
  | nil => rfl
  | cons link rest induction =>
    cases selected : link.parent with
    | missing => simpa [parentInsertionMatches, selected] using induction
    | mismatch other =>
      by_cases same : other = position <;> simpa [parentInsertionMatches, selected, same] using induction
    | located other key =>
      by_cases same : other = position <;> simp [parentInsertionMatches, selected, same, induction]

/-- For every state with the global counter bound, running actual new-row checks
and then appending a stored row preserves the bound on success. Stops satisfy the
stop-bound predicate. Rows must be aligned and stored; the enlarged target table must
have unique rowids and selected keys. Parent scans must agree with lookups, and self-parent
shortcuts must be sound for the selected child links. Either scan flag is allowed.
This phase law covers no stale UPDATE row, actions or triggers. Proof sketch: the global
append equation bounds the new violations by failed child checks; the actual counter
delta pays for those checks and all enabled parent scans. -/
theorem newSteps_append_parent_counterBound {catalog : Catalog} {state : KeyState} {position : Nat} {table : Table}
    (bound : state.CounterBound catalog) (present : (state.database catalog).table position = some table)
    (aligned : position < state.rows.length) (stored : (state.database catalog).RowsStored)
    (new : Row) (newStored : new.Stored table.shape.columns)
    (unique : ({table with rows := table.rows ++ [new]} : Table).KeysUnique (catalog.uniqueKeys position table.shape))
    (distinct : ({table with rows := table.rows ++ [new]} : Table).RowidsDistinct)
    (consistent : ∀ link ∈ catalog.foreignKeyLinks, ∀ key child,
      link.parent = .located position key → (state.database catalog).table link.child = some child →
      link.LookupScanConsistent child.shape table.shape key)
    (selectedUnique : ∀ link ∈ catalog.foreignKeyLinks, ∀ pairs,
      link.parent = .located position (.columns pairs) →
      UniqueKey.ofColumns table.shape.columns (pairs.map Prod.snd) ∈ catalog.uniqueKeys position table.shape)
    (selfSound : ∀ link ∈ childLinks catalog.foreignKeyLinks position, ∀ key,
      link.parent = .located position key → link.SelfLookupSound table.shape key) (scan : Bool) :
    ResultHolds (KeyState.CounterBound catalog) (KeyStop.CounterBound catalog)
      ((fun reached => reached.changeRows position (· ++ [new])) <$>
        newSteps catalog state position new (childLinks catalog.foreignKeyLinks position)
          (parentLinks catalog.foreignKeyLinks position) scan none []) := by
  have appended := Database.foreignKeyViolations_append_parent present aligned stored new newStored
    unique distinct consistent selectedUnique
  rw [parentInsertionMatches_sum] at appended
  have count : (childLinks catalog.foreignKeyLinks position).countP
      (fun link => !link.satisfied ((state.database catalog).setRows position (table.rows ++ [new])) new) ≤
      (childLinks catalog.foreignKeyLinks position).countP
        (fun link => !newRowSatisfied (state.database catalog) position new none [] link) := by
    apply List.countP_mono_left
    intro link member failed
    have sound := ForeignKeyLink.newRowSatisfied_append present aligned link new newStored (selfSound link member)
    cases check : newRowSatisfied (state.database catalog) position new none [] link with
    | false => rfl
    | true => simp [sound check] at failed
  have lower := newSteps_counter_delta catalog state position new
    (childLinks catalog.foreignKeyLinks position) (parentLinks catalog.foreignKeyLinks position) scan none []
  have kept := newSteps_rows catalog state position new
    (childLinks catalog.foreignKeyLinks position) (parentLinks catalog.foreignKeyLinks position) scan none []
  have tableRows : table.rows = state.rows.getD position [] := by
    obtain ⟨shape, _, equal⟩ := Option.map_eq_some_iff.mp present
    subst table
    rfl
  cases result : newSteps catalog state position new
      (childLinks catalog.foreignKeyLinks position) (parentLinks catalog.foreignKeyLinks position) scan none [] with
  | error stop =>
    rw [result] at kept
    dsimp only [ResultHolds] at kept
    subst stop
    trivial
  | ok reached =>
    rw [result] at kept lower
    dsimp only [ResultHolds] at kept lower
    change (reached.changeRows position (· ++ [new])).CounterBound catalog
    have same : (reached.changeRows position (· ++ [new])).database catalog =
        (state.database catalog).setRows position (table.rows ++ [new]) := by
      simp only [KeyState.changeRows, KeyState.database, Database.setRows, kept, tableRows]
    unfold KeyState.CounterBound
    rw [same]
    change ((_ : Nat) : Int) ≤ reached.counter
    unfold KeyState.CounterBound at bound
    dsimp only [KeyState.database] at appended lower bound count ⊢
    cases scan <;> simp only [Bool.false_eq_true, ite_false, ite_true] at lower <;> omega

end Belay.Sqlite.Model
