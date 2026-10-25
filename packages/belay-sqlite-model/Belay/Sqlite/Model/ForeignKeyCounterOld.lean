import Belay.Sqlite.Model.RowEngineKeySteps

set_option doc.verso true

/-! Counter arithmetic for the old-row phase of deletion and update. Its child checks can
remove at most one count per unsatisfied link; its parent scans only add counts. -/

namespace Belay.Sqlite.Model

/-- For every catalog, state, row and link lists, processing two consecutive child-link lists
is exactly the bind of processing the first without parent scans and then the rest with all
parent scans. Stops propagate unchanged. Proof sketch: the child fold over append is two
bound folds; the empty intermediate parent fold is the identity. -/
theorem oldSteps_children_append (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (first rest parents : List ForeignKeyLink) (ignore : Bool) :
    oldSteps catalog state position row (first ++ rest) parents ignore =
      (oldSteps catalog state position row first [] ignore >>= fun reached =>
        oldSteps catalog reached position row rest parents ignore) := by
  simp only [oldSteps, List.foldlM_append, List.foldlM_nil]
  simp only [bind_assoc, pure_bind]

/-- For every old-row phase with no child checks, a successful result has a counter at least
the input counter. An error requires nothing. The parent scans only add nonnegative row
counts, including when DROP ignores an unsupported parent. Proof sketch: fold induction
preserves the lower bound; an unsupported nonignored link stops the phase. -/
theorem oldSteps_parents_counter (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (parents : List ForeignKeyLink) (ignore : Bool) :
    ResultHolds (fun after => state.counter ≤ after.counter) (fun _ => True)
      (oldSteps catalog state position row [] parents ignore) := by
  simp only [oldSteps, List.foldlM_nil, pure_bind]
  apply ResultHolds.foldlM
  · intro reached link good
    split
    · rename_i parent key selected
      change state.counter ≤ reached.counter + _
      have nonnegative : (0 : Int) ≤ (childRows (reached.database catalog) link key position row [] true).length := by omega
      omega
    all_goals split
    all_goals first | exact good | trivial
  · exact Int.le_refl _

/-- For every old row and one child link, a successful child check retains all rows and
reduces the counter by at most one when that link is unsatisfied, or by zero when satisfied.
An error requires nothing. This includes DROP's missing-parent fallback. Proof sketch:
inspect the selected parent, NULL test and lookup; each branch skips, decrements or stops. -/
theorem oldSteps_single_counter (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (link : ForeignKeyLink) (ignore : Bool) :
    ResultHolds (fun after => after.rows = state.rows ∧
      state.counter - (if link.satisfied (state.database catalog) row then 0 else 1) ≤ after.counter)
      (fun _ => True) (oldSteps catalog state position row [link] [] ignore) := by
  simp only [oldSteps, List.foldlM_cons, List.foldlM_nil, bind_pure]
  repeat' (first | split | dsimp only)
  all_goals simp_all [ResultHolds, ForeignKeyLink.satisfied, KeyState.database, pure, Except.pure, throw]
  all_goals try trivial
  all_goals omega

/-- For every old-row phase, a successful counter is at least its initial value minus the
number of supplied child links unsatisfied by that row in the input database. Duplicate
links count separately. Parent scans can increase this bound, and errors impose no condition.
Proof sketch: split off one child check, use its row equality for the remaining comparisons,
and add its decrement bound to the induction hypothesis. With no children, parent scans only
increase the counter. This arithmetic does not yet assert a bound on database violations. -/
theorem oldSteps_counter_lower (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (children parents : List ForeignKeyLink) (ignore : Bool) :
    ResultHolds (fun after => state.counter -
      (children.countP fun link => !link.satisfied (state.database catalog) row) ≤ after.counter)
      (fun _ => True) (oldSteps catalog state position row children parents ignore) := by
  induction children generalizing state with
  | nil => simpa using oldSteps_parents_counter catalog state position row parents ignore
  | cons link rest induction =>
    rw [show link :: rest = [link] ++ rest from rfl, oldSteps_children_append]
    apply ResultHolds.bind (oldSteps_single_counter catalog state position row link ignore)
    intro reached good
    have same : reached.database catalog = state.database catalog := by
      simp only [KeyState.database, good.1]
    apply (induction reached).mono
    intro after later
    rw [same] at later
    simp only [List.countP_append, List.countP_singleton]
    cases satisfied : link.satisfied (state.database catalog) row <;>
      simp [satisfied] at good ⊢ <;> omega

end Belay.Sqlite.Model
