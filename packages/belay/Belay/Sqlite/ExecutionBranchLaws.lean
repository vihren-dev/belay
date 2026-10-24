import Belay.Sqlite.ExecutionBranches

set_option doc.verso true

namespace Belay.Sqlite
open Model

/-- Every actual run is a permitted branch, for every program, clock, starting index and
connection. Thus the branch set is never empty, even when the run stops unmodeled.
Proof sketch: induction on the program always chooses the actual raw output. -/
theorem Sql.Branch.actual {α : Type} (program : Sql α) :
    ∀ clock index connection, program.Branch clock index connection (program.runFrom clock index connection) := by
  induction program with
  | pure value => exact fun clock index connection => .pure value clock index connection
  | exec statement values rest later =>
    intro clock index connection
    simp only [Sql.runFrom]
    cases step : runScriptStep runContext clock index connection statement values with
    | ended reason => exact .stopped step
    | continued output next => exact .continued step (.actual output) (later output clock (index + 1) next)

/-- For every pure program and proposed result, the branch relation holds exactly when
that result returns the pure value, leaves the full connection unchanged, and has no outputs.
Proof sketch: invert the sole branch constructor for a pure program. -/
theorem Sql.branch_pure_iff {α : Type} (value : α) (clock : Option Clock) (index : Nat)
    (connection : Connection) (result : SqlRun α) :
    (Sql.pure value).Branch clock index connection result ↔
      result = { outputs := [], connection, value := some value } := by
  constructor
  · intro branch; cases branch; rfl
  · rintro rfl; exact .pure value clock index connection

/-- For a step that stops with the stated reason, a proposed branch is exactly its stopped
result. It keeps the input connection, records one unmodeled output and has no value.
Proof sketch: invert the branch constructors and rule out a continuing step. -/
theorem Sql.branch_stopped_iff {α : Type} {statement values} {rest : Output → Sql α}
    {clock index connection reason} (step :
      runScriptStep runContext clock index connection statement values = .ended reason)
    (result : SqlRun α) : (.exec statement values rest : Sql α).Branch clock index connection result ↔
      result = { outputs := [.unmodeled reason], connection, value := none } := by
  constructor
  · intro branch
    cases branch with
    | stopped other => cases step.symm.trans other; rfl
    | continued other _ _ => cases step.symm.trans other
  · rintro rfl; exact .stopped step

/-- For a continuing step, a proposed branch is exactly an allowed selected output followed
by a branch of its continuation from the actual next connection and index. The selected
output prefixes that branch's trace. Proof sketch: invert the branch constructors. -/
theorem Sql.branch_continued_iff {α : Type} {statement values} {rest : Output → Sql α}
    {clock index connection actual next} (step :
      runScriptStep runContext clock index connection statement values = .continued actual next)
    (result : SqlRun α) : (.exec statement values rest : Sql α).Branch clock index connection result ↔
      ∃ selected later, OutputChoice actual selected ∧ (rest selected).Branch clock (index + 1) next later ∧
        result = { later with outputs := selected :: later.outputs } := by
  constructor
  · intro branch
    cases branch with
    | stopped other => cases step.symm.trans other
    | continued other choice later =>
      cases step.symm.trans other
      exact ⟨_, _, choice, later, rfl⟩
  · rintro ⟨selected, later, choice, branch, rfl⟩
    exact .continued step choice branch

/-- Every permitted branch preserves validity of the current database and any open
transaction snapshot, assuming both are valid initially under the pinned profile.
Proof sketch: induction on the branch uses the existing single-step validity theorem;
all choices share that step's actual next connection. -/
theorem Sql.Branch.valid {α : Type} {program : Sql α} {clock index connection result}
    (branch : program.Branch clock index connection result)
    (valid : connection.state.Holds (Database.Valid Profile.pinned)) :
    result.connection.state.Holds (Database.Valid Profile.pinned) := by
  induction branch with
  | pure => exact valid
  | stopped => exact valid
  | continued step _ _ later =>
    exact later (runScriptStep_valid runContext _ _ _ _ rfl rfl valid step)

end Belay.Sqlite
