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
    | continued output next others =>
      exact Sql.Branch.continued_own step (.actual output) (later output clock (index + 1) next)

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
    | continued other _ _ _ => cases step.symm.trans other
  · rintro rfl; exact .stopped step

/-- For a continuing step with no further execution ({lit}`others = []`, as for every statement that is no
INSERT from a query), the chosen execution of a branch is the step's own. Proof sketch: the only
execution of the step is its own ({name}`RunStep.executions`). -/
theorem Sql.Branch.found_eq {clock index connection statement values actual next found}
    (_step : runScriptStep runContext clock index connection statement values = .continued actual next [])
    (member : found ∈ (RunStep.continued actual next []).executions) :
    found = { output := actual, next } := by
  simpa [RunStep.executions] using member

/-- For a continuing step, a proposed branch is exactly a chosen execution of the statement
({name}`RunStep.executions`), an allowed selected output of that execution, and a branch of the
continuation from the next connection of that execution and the next index. The selected output
prefixes that branch's trace. Proof sketch: invert the branch constructors. -/
theorem Sql.branch_continued_executions_iff {α : Type} {statement values} {rest : Output → Sql α}
    {clock index connection actual next others} (step :
      runScriptStep runContext clock index connection statement values = .continued actual next others)
    (result : SqlRun α) : (.exec statement values rest : Sql α).Branch clock index connection result ↔
      ∃ found ∈ (RunStep.continued actual next others).executions, ∃ selected later,
        OutputChoice found.output selected ∧ (rest selected).Branch clock (index + 1) found.next later ∧
        result = { later with outputs := selected :: later.outputs } := by
  constructor
  · intro branch
    cases branch with
    | stopped other => cases step.symm.trans other
    | continued other member choice later =>
      cases step.symm.trans other
      exact ⟨_, member, _, _, choice, later, rfl⟩
  · rintro ⟨found, member, selected, later, choice, branch, rfl⟩
    exact .continued step member choice branch

/-- For a continuing step, a proposed branch is exactly an allowed selected output followed
by a branch of its continuation from the actual next connection and index. The selected
output prefixes that branch's trace. A step with no further execution ({lit}`others = []`, as for every
statement that is no INSERT from a query; the proof {lit}`single` is found by {lit}`rfl` when the step's type shows it) has the step's own execution as its only one. Proof sketch:
{name}`Sql.branch_continued_executions_iff` with the one execution of the step. -/
theorem Sql.branch_continued_iff {α : Type} {statement values} {rest : Output → Sql α}
    {clock index connection actual next others} (step :
      runScriptStep runContext clock index connection statement values = .continued actual next others)
    (result : SqlRun α) (single : others = [] := by rfl) :
    (.exec statement values rest : Sql α).Branch clock index connection result ↔
      ∃ selected later, OutputChoice actual selected ∧ (rest selected).Branch clock (index + 1) next later ∧
        result = { later with outputs := selected :: later.outputs } := by
  subst single
  rw [Sql.branch_continued_executions_iff step]
  simp [RunStep.executions]

/-- Every permitted branch preserves validity of the current database and any open
transaction snapshot, assuming both are valid initially under the pinned profile.
Proof sketch: induction on the branch uses the existing single-step validity theorem;
every execution of the step keeps validity ({name}`runScriptStep_valid`). -/
theorem Sql.Branch.valid {α : Type} {program : Sql α} {clock index connection result}
    (branch : program.Branch clock index connection result)
    (valid : connection.state.Holds (Database.Valid Profile.pinned)) :
    result.connection.state.Holds (Database.Valid Profile.pinned) := by
  induction branch with
  | pure => exact valid
  | stopped => exact valid
  | continued step member _ _ ih =>
    exact ih (runScriptStep_valid runContext _ _ _ _ rfl rfl valid _ (by rw [step]; exact member))

end Belay.Sqlite
