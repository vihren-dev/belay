import Belay.Sqlite.Model.ForeignKeyCounterRun
import Belay.Sqlite.Model.RowEngineKeySteps

set_option doc.verso true

/-! Counter arithmetic of the existing new-row foreign-key phase. -/

namespace Belay.Sqlite.Model

/-- The child check used before a new row is stored: selected NULL values exempt it;
otherwise lookup reads current parent rows, a permitted stale self row, and the self-parent
shortcut. Missing definitions or mappings give false. Use {lean}`none` for a fresh INSERT. -/
def newRowSatisfied (database : Database) (position : Nat) (row : Row) (stale : Option Row)
    (changed : List Nat) (link : ForeignKeyLink) : Bool :=
  link.hasNull row.values || match link.parent with
    | .located parent key => match database.catalog.tableAt parent with
      | none => false
      | some shape => parentFound shape key link row.values
          (database.rowsAt parent ++ (if parent == position then staleRows key stale changed else []))
          (if parent == position then some row else none)
    | .missing | .mismatch _ => false

/-- The sum of matching child scans for located parent links before a new row is
stored. A self-table scan also reads the supplied stale row. Missing or mismatched links
contribute zero; the actual phase separately rejects those links. Use {lean}`none` for INSERT. -/
def parentDecrements (database : Database) (position : Nat) (row : Row) (stale : Option Row)
    (parents : List ForeignKeyLink) : Nat :=
  (parents.map fun link => match link.parent with
    | .located _ key => (childRows database link key position row
        (if link.child == position then stale.toList else []) false).length
    | .missing | .mismatch _ => 0).sum

/-- For every split child-link list, the actual new-row phase equals its first child
checks followed by the remaining child checks and parent scans. Proof sketch: fold append
and associativity of the existing exception monad. -/
theorem newSteps_children_append (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (first rest parents : List ForeignKeyLink) (scan : Bool) (stale : Option Row) (changed : List Nat) :
    newSteps catalog state position row (first ++ rest) parents scan stale changed =
      (newSteps catalog state position row first [] false stale changed >>= fun reached =>
        newSteps catalog reached position row rest parents scan stale changed) := by
  simp only [newSteps, List.foldlM_append, List.foldlM_nil, Bool.not_false, ite_true, bind_pure]
  simp only [bind_assoc]

/-- For every input and single child link, a successful new-row child check keeps
rows and adds one exactly when {name}`newRowSatisfied` is false. A stop requires nothing.
Proof sketch: inspect the existing phase branches. -/
theorem newSteps_child_single (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (link : ForeignKeyLink) (stale : Option Row) (changed : List Nat) :
    ResultHolds (fun after => after.rows = state.rows ∧ after.counter = state.counter +
      (if newRowSatisfied (state.database catalog) position row stale changed link then 0 else 1))
      (fun _ => True) (newSteps catalog state position row [link] [] false stale changed) := by
  simp only [newSteps, List.foldlM_cons, List.foldlM_nil, Bool.not_false, ite_true, bind_pure]
  repeat' (first | split | dsimp only)
  all_goals simp_all [ResultHolds, newRowSatisfied, KeyState.database, pure, Except.pure, throw]
  all_goals try trivial
  all_goals omega

/-- For every child-link list, successful child checks keep rows and add exactly
the number of false {name}`newRowSatisfied` checks. A stop requires nothing.
Proof sketch: list induction composes the single-link equation. -/
theorem newSteps_children_exact (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (children : List ForeignKeyLink) (stale : Option Row) (changed : List Nat) :
    ResultHolds (fun after => after.rows = state.rows ∧ after.counter = state.counter +
      children.countP (fun link => !newRowSatisfied (state.database catalog) position row stale changed link))
      (fun _ => True) (newSteps catalog state position row children [] false stale changed) := by
  induction children generalizing state with
  | nil => exact ⟨rfl, by simp⟩
  | cons link rest induction =>
    rw [show link :: rest = [link] ++ rest from rfl, newSteps_children_append]
    apply ResultHolds.bind (newSteps_child_single catalog state position row link stale changed)
    intro reached good
    apply (induction reached).mono
    intro after later
    have same : reached.database catalog = state.database catalog := by simp [KeyState.database, good.1]
    refine ⟨later.1.trans good.1, ?_⟩
    rw [same, good.2] at later
    cases satisfied : newRowSatisfied (state.database catalog) position row stale changed link <;>
      simp [satisfied] at good later ⊢ <;> omega

/-- For every split parent-link list, the new-row parent phase equals the first
scans followed by the remaining scans. Proof sketch: the fold append equation. -/
theorem newSteps_parents_append (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (first rest : List ForeignKeyLink) (stale : Option Row) (changed : List Nat) :
    newSteps catalog state position row [] (first ++ rest) true stale changed =
      (newSteps catalog state position row [] first true stale changed >>= fun reached =>
        newSteps catalog reached position row [] rest true stale changed) := by
  simp only [newSteps, List.foldlM_nil, pure_bind, Bool.not_true, Bool.false_eq_true, ite_false, List.foldlM_append]

/-- For every single parent link, a successful new-row scan keeps rows and lowers
the counter by at most its matching-child count. A zero counter skips the subtraction;
a stop requires nothing. Proof sketch: inspect the existing scan branches. -/
theorem newSteps_parent_single (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (link : ForeignKeyLink) (stale : Option Row) (changed : List Nat) :
    ResultHolds (fun after => after.rows = state.rows ∧ state.counter -
      parentDecrements (state.database catalog) position row stale [link] ≤ after.counter)
      (fun _ => True) (newSteps catalog state position row [] [link] true stale changed) := by
  simp only [newSteps, List.foldlM_cons, List.foldlM_nil, pure_bind, bind_pure,
    Bool.not_true, Bool.false_eq_true, ite_false]
  repeat' (first | split | dsimp only)
  all_goals simp_all [ResultHolds, parentDecrements, pure, Except.pure, throw]
  all_goals try trivial
  all_goals omega

/-- For every parent-link list, successful new-row scans keep rows and lower the
counter by at most {name}`parentDecrements`. A stop requires nothing.
Proof sketch: list induction adds the single-link bounds. -/
theorem newSteps_parents_lower (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (parents : List ForeignKeyLink) (stale : Option Row) (changed : List Nat) :
    ResultHolds (fun after => after.rows = state.rows ∧ state.counter -
      parentDecrements (state.database catalog) position row stale parents ≤ after.counter)
      (fun _ => True) (newSteps catalog state position row [] parents true stale changed) := by
  induction parents generalizing state with
  | nil => exact ⟨rfl, by simp [parentDecrements]⟩
  | cons link rest induction =>
    rw [show link :: rest = [link] ++ rest from rfl, newSteps_parents_append]
    apply ResultHolds.bind (newSteps_parent_single catalog state position row link stale changed)
    intro reached good
    apply (induction reached).mono
    intro after later
    have same : reached.database catalog = state.database catalog := by simp [KeyState.database, good.1]
    refine ⟨later.1.trans good.1, ?_⟩
    rw [same] at later
    simp only [parentDecrements, List.map_append, List.sum_append, Int.natCast_add]
    simp only [parentDecrements] at later good
    omega

/-- For every new-row phase, its successful counter is at least the input counter
plus failed child checks, minus matching parent scans when scanning is enabled.
A stop requires nothing. Proof sketch: compose exact child arithmetic with the parent
scan bound; disabling scans leaves their contribution zero. -/
theorem newSteps_counter_delta (catalog : Catalog) (state : KeyState) (position : Nat) (row : Row)
    (children parents : List ForeignKeyLink) (scan : Bool) (stale : Option Row) (changed : List Nat) :
    ResultHolds (fun after => state.counter +
      children.countP (fun link => !newRowSatisfied (state.database catalog) position row stale changed link) -
      (if scan then parentDecrements (state.database catalog) position row stale parents else 0) ≤ after.counter)
      (fun _ => True) (newSteps catalog state position row children parents scan stale changed) := by
  have splitRun := newSteps_children_append catalog state position row children [] parents scan stale changed
  simp only [List.append_nil] at splitRun
  rw [splitRun]
  apply ResultHolds.bind (newSteps_children_exact catalog state position row children stale changed)
  intro reached good
  have same : reached.database catalog = state.database catalog := by simp [KeyState.database, good.1]
  cases scan with
  | false =>
    change state.counter +
      children.countP (fun link => !newRowSatisfied (state.database catalog) position row stale changed link) - 0 ≤ reached.counter
    omega
  | true =>
    apply (newSteps_parents_lower catalog reached position row parents stale changed).mono
    intro after later
    rw [same] at later
    simp only [ite_true, good.2] at later ⊢
    omega

end Belay.Sqlite.Model
