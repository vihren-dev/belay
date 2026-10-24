import Belay.Sqlite.Model.ForeignKeyCounterOld

set_option doc.verso true

/-! Exact parent-scan increments complete the old-row counter bound. -/

namespace Belay.Sqlite.Model

/-- Count the child rows visited by the supplied old-row parent scans. Located links
contribute their scan length; missing or incompatible parents contribute zero. Duplicate
links contribute separately. An empty parent list has count zero. -/
def parentIncrements (database : Database) (position : Nat) (row : Row) (parents : List ForeignKeyLink) : Nat :=
  (parents.map fun link => match link.parent with
    | .located _ key => (childRows database link key position row [] true).length
    | .missing | .mismatch _ => 0).sum

/-- For every old-row phase without child checks, consecutive parent lists execute as two
bound phases in the same order. Stops propagate unchanged. Proof sketch: fold over append. -/
theorem oldSteps_parents_append (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (first rest : List ForeignKeyLink) (ignore : Bool) :
    oldSteps catalog state position row [] (first ++ rest) ignore =
      (oldSteps catalog state position row [] first ignore >>= fun reached =>
        oldSteps catalog reached position row [] rest ignore) := by
  simp only [oldSteps, List.foldlM_nil, pure_bind, List.foldlM_append]

/-- For every single old-row parent scan, a successful result retains all rows and adds
exactly its scan count to the counter. Errors require nothing. Proof sketch: inspect the
parent classification; located scans add their length and ignored unsupported links add zero. -/
theorem oldSteps_parent_single (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (link : ForeignKeyLink) (ignore : Bool) :
    ResultHolds (fun after => after.rows = state.rows ∧ after.counter = state.counter +
      parentIncrements (state.database catalog) position row [link]) (fun _ => True)
      (oldSteps catalog state position row [] [link] ignore) := by
  simp only [oldSteps, List.foldlM_nil, pure_bind, List.foldlM_cons, bind_pure]
  repeat' (first | split | dsimp only)
  all_goals simp_all [ResultHolds, parentIncrements, pure, Except.pure, throw]
  all_goals trivial

/-- For every old-row parent list without child checks, success retains all rows and adds
exactly the sum of scan counts to the counter. Errors require nothing. Proof sketch: split
the first scan, use row equality for the rest, and add their exact increments. -/
theorem oldSteps_parent_exact (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (parents : List ForeignKeyLink) (ignore : Bool) :
    ResultHolds (fun after => after.rows = state.rows ∧ after.counter = state.counter +
      parentIncrements (state.database catalog) position row parents) (fun _ => True)
      (oldSteps catalog state position row [] parents ignore) := by
  induction parents generalizing state with
  | nil => exact ⟨rfl, by simp [parentIncrements]⟩
  | cons link rest induction =>
    rw [show link :: rest = [link] ++ rest from rfl, oldSteps_parents_append]
    apply ResultHolds.bind (oldSteps_parent_single catalog state position row link ignore)
    intro reached good
    apply (induction reached).mono
    intro after later
    have same : reached.database catalog = state.database catalog := by simp [KeyState.database, good.1]
    refine ⟨later.1.trans good.1, ?_⟩
    rw [same, good.2] at later
    simp only [parentIncrements, List.map_append, List.sum_append, Int.natCast_add]
    simp only [parentIncrements] at later
    omega

/-- For every old-row phase, a successful counter is at least its initial counter minus
the supplied unsatisfied child-link count plus the supplied parent-scan count. Errors require
nothing, and duplicate links count separately. Proof sketch: separate child checks from parent
scans and combine their decrement bound and exact increment using unchanged rows. -/
theorem oldSteps_counter_delta (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (children parents : List ForeignKeyLink) (ignore : Bool) :
    ResultHolds (fun after => state.counter -
      (children.countP fun link => !link.satisfied (state.database catalog) row) +
      parentIncrements (state.database catalog) position row parents ≤ after.counter)
      (fun _ => True) (oldSteps catalog state position row children parents ignore) := by
  have splitRun := oldSteps_children_append catalog state position row children [] parents ignore
  simp only [List.append_nil] at splitRun
  rw [splitRun]
  have lower := oldSteps_counter_lower catalog state position row children [] ignore
  have rows := oldSteps_rows catalog state position row children [] ignore
  cases result : oldSteps catalog state position row children [] ignore with
  | error stop => trivial
  | ok reached =>
    rw [result] at lower rows
    dsimp only [ResultHolds] at lower rows
    change ResultHolds _ _ (oldSteps catalog reached position row [] parents ignore)
    apply (oldSteps_parent_exact catalog reached position row parents ignore).mono
    intro after good
    have same : reached.database catalog = state.database catalog := by simp [KeyState.database, rows]
    rw [same] at good
    omega

end Belay.Sqlite.Model
