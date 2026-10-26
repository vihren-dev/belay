import Belay.Sqlite.ExecutionViewEquivalence
import Belay.Sqlite.ExecutionEquivalence
import Belay.Sqlite.ExecutionBranchLaws
import Belay.Sqlite.ScopedAgreement

set_option doc.verso true

/-! Programs with one branch (ADR 0017, S8). A branch can choose among the concrete results of a
statement whose rows have no promised order ({name}`Belay.Sqlite.Model.Output.oneOf`). A program whose steps give no such
output has exactly one branch, its actual run. The check is a computation, so a proof for a concrete
program can use {lit}`decide +kernel` or {lit}`rfl` for it. Equivalence of two such programs at a
context then reduces to equality of their actual runs. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- Whether an output is a choice between results ({name}`Belay.Sqlite.Model.Output.oneOf`). -/
def Model.Output.choosesResults : Output → Bool
  | .oneOf _ => true
  | .rows _ | .done _ | .error _ | .unmodeled _ => false

/-- Whether the program has one branch from the clock, index and connection: every continued step
along the actual run gives an output that is not a choice between results. A stopped step has one
branch by itself. The check follows the actual run only; it reads no other branch, because it
shows that there is none. -/
def Sql.hasOneBranch {α : Type} (clock : Option Clock) : Sql α → Nat → Connection → Bool
  | .pure _, _, _ => true
  | .exec statement values rest, index, connection =>
    match runScriptStep runContext clock index connection statement values with
    | .ended _ => true
    | .continued output next =>
      !Model.Output.choosesResults output && (rest output).hasOneBranch clock (index + 1) next

/-- For every program that has one branch from a context, a result is a branch of the program exactly
when it is the actual run. Proof sketch: induction on the program. A pure program and a stopped step
have only their own result. After a continued step, the output is not a choice between results, so the
only permitted output is the actual one, and the claim for the rest applies. -/
theorem Sql.branch_iff_actual {α : Type} (program : Sql α) :
    ∀ (clock : Option Clock) (index : Nat) (connection : Connection) (result : SqlRun α),
      program.hasOneBranch clock index connection = true →
        (program.Branch clock index connection result ↔ result = program.runFrom clock index connection) := by
  induction program with
  | pure value =>
    intro clock index connection result _
    rw [Sql.branch_pure_iff]
    rfl
  | exec statement values rest later =>
    intro clock index connection result one
    cases step : runScriptStep runContext clock index connection statement values with
    | ended reason =>
      rw [Sql.branch_stopped_iff step]
      simp [Sql.runFrom, step]
    | continued output next =>
      simp only [Sql.hasOneBranch, step, Bool.and_eq_true, Bool.not_eq_true'] at one
      obtain ⟨notChoice, restOne⟩ := one
      have only : ∀ selected, OutputChoice output selected → selected = output := by
        intro selected choice
        rcases choice with same | other
        · exact same
        · cases output <;> simp_all [Model.Output.choosesResults]
      rw [Sql.branch_continued_iff step]
      simp only [Sql.runFrom, step]
      constructor
      · rintro ⟨selected, tail, choice, branch, rfl⟩
        obtain rfl := only selected choice
        rw [(later selected clock (index + 1) next tail restOne).1 branch]
      · rintro rfl
        exact ⟨output, _, .inl rfl, (Sql.Branch.actual (rest output) clock (index + 1) next), rfl⟩

/-- Two programs that each have one branch at a context are equivalent there when their actual runs
are equal. Both sides have the same single result, so the actual runs and the branch sets agree. -/
theorem Sql.EquivAt.of_one_branch {α : Type} {first second : Sql α} {state : ExecutionContext}
    (leftOne : first.hasOneBranch state.clock state.index state.connection = true)
    (rightOne : second.hasOneBranch state.clock state.index state.connection = true)
    (same : first.runFrom state.clock state.index state.connection =
      second.runFrom state.clock state.index state.connection) :
    first.EquivAt second state :=
  ⟨same, fun result => by
    rw [Sql.branch_iff_actual first _ _ _ result leftOne, Sql.branch_iff_actual second _ _ _ result rightOne,
      same]⟩

/-- Two programs that each have one branch at a context have equal views there when the projected
actual observations are equal. Proof sketch: each side realizes exactly its projected actual
observation, so the two realization conditions both say "equals that observation". -/
theorem Sql.View.EquivAt.of_one_branch {α : Type} {first second : Sql α}
    {left : Sql.View first} {right : Sql.View second} {state : ExecutionContext}
    (leftOne : first.hasOneBranch state.clock state.index state.connection = true)
    (rightOne : second.hasOneBranch state.clock state.index state.connection = true)
    (same : left.fullObservation state (first.runFrom state.clock state.index state.connection) =
      right.fullObservation state (second.runFrom state.clock state.index state.connection)) :
    left.EquivAt right state :=
  ⟨same, fun observation => by
    constructor
    · rintro ⟨result, branch, rfl⟩
      rw [Sql.branch_iff_actual first _ _ _ result leftOne] at branch
      exact ⟨_, Sql.Branch.actual second _ _ _, by rw [branch, ← same]⟩
    · rintro ⟨result, branch, rfl⟩
      rw [Sql.branch_iff_actual second _ _ _ result rightOne] at branch
      exact ⟨_, Sql.Branch.actual first _ _ _, by rw [branch, same]⟩⟩

/-- Two programs that each have one branch at two contexts agree under a relation when their actual
runs agree. The one branch of each program is its actual run, so the forward and the backward cover
follow from the actual agreement. Proof sketch: a branch of either side equals its actual run, which
the actual agreement matches with the actual run of the other side. -/
theorem Sql.ScopedAt.of_one_branch {α : Type} {related : ExecutionContext → ExecutionContext → Prop}
    {left right : Sql α} {first second : ExecutionContext}
    (leftOne : left.hasOneBranch first.clock first.index first.connection = true)
    (rightOne : right.hasOneBranch second.clock second.index second.connection = true)
    (agree : RunsAgree related first second
      (left.runFrom first.clock first.index first.connection)
      (right.runFrom second.clock second.index second.connection)) :
    Sql.ScopedAt related left right first second :=
  ⟨agree,
    fun one branch => ⟨_, Sql.Branch.actual right _ _ _, by
      rw [(Sql.branch_iff_actual left _ _ _ one leftOne).1 branch]; exact agree⟩,
    fun one branch => ⟨_, Sql.Branch.actual left _ _ _, by
      rw [(Sql.branch_iff_actual right _ _ _ one rightOne).1 branch]
      exact ⟨agree.1.symm, agree.2.1.symm, agree.2.2⟩⟩⟩

/-- For every program, every clock that gives one date at every index (or no clock), every pair of start
indices and every connection: the check {name}`Sql.hasOneBranch` gives the same answer at both indices.
Plain words: whether a program has one branch does not depend on the start index when the clock is
constant. Proof sketch: induction on the program. One step runs the same at both indices
({name}`runScriptStep_index`), so the output and the connection that the check reads are equal. -/
theorem Sql.hasOneBranch_index {α : Type} (program : Sql α) (clock : Option Clock)
    (constant : ∀ assignment ∈ clock, ∀ one other, assignment one = assignment other) :
    ∀ (first second : Nat) (connection : Connection),
      program.hasOneBranch clock first connection = program.hasOneBranch clock second connection := by
  induction program with
  | pure value => intro first second connection; rfl
  | exec statement values rest later =>
    intro first second connection
    have same := runScriptStep_index runContext clock first second connection statement values
      (fun assignment member => constant assignment member _ _)
    simp only [Sql.hasOneBranch, same]
    cases runScriptStep runContext clock second connection statement values with
    | ended reason => rfl
    | continued output next => simp only [later output (first + 1) (second + 1) next]

/-- Two programs that each have one branch at a context have equal weak views there when the projected
actual observations are equal. Proof sketch: each side realizes exactly its projected actual
observation, so the two realization conditions both say "equals that observation". -/
theorem Sql.View.ObservationEquivAt.of_one_branch {α : Type} {first second : Sql α}
    {left : Sql.View first} {right : Sql.View second} {state : ExecutionContext}
    (leftOne : first.hasOneBranch state.clock state.index state.connection = true)
    (rightOne : second.hasOneBranch state.clock state.index state.connection = true)
    (same : left.observation (first.runFrom state.clock state.index state.connection) =
      right.observation (second.runFrom state.clock state.index state.connection)) :
    left.ObservationEquivAt right state :=
  ⟨same, fun observation => by
    constructor
    · rintro ⟨result, branch, rfl⟩
      rw [Sql.branch_iff_actual first _ _ _ result leftOne] at branch
      exact ⟨_, Sql.Branch.actual second _ _ _, by rw [branch, ← same]⟩
    · rintro ⟨result, branch, rfl⟩
      rw [Sql.branch_iff_actual second _ _ _ result rightOne] at branch
      exact ⟨_, Sql.Branch.actual first _ _ _, by rw [branch, same]⟩⟩

end Belay.Sqlite
