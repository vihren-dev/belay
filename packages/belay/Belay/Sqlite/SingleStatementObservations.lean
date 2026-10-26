import Belay.Sqlite.ExecutionBranchLaws
import Belay.Sqlite.ProgramLaws
import Belay.Sqlite.ExecutionObservations

set_option doc.verso true

/-! The observations of a program that sends one statement (ADR 0017, S6). They depend only on the
output of the statement's step: the actual run gives that output, and the branches give each output
that {lit}`OutputChoice` permits. Two such programs with equal step outputs, at any inputs, have equal
actual observations and equal sets of branch observations. -/

namespace Belay.Sqlite
open Model

/-- The observation of a program that sends one statement, when the statement's step has this output
and the run or branch selects this output: no value when the step stops the run, otherwise the list
of the selected output, and always the one-output trace. -/
def singleObservation (output selected : Output) : Option (List Output) × List Output :=
  (if output.endsRun then none else some [selected], [selected])

/-- For every statement, values and inputs, the actual observation of the program that sends the
statement is {name}`singleObservation` of the step's output with itself. Proof sketch: case analysis on the
step; a continuing output does not end the run ({name}`runScriptStep_continued`). -/
theorem sendStatements_single_actual (statement : Syntax.Statement) (values : List Value)
    (clock : Option Clock) (index : Nat) (connection : Connection) :
    ((sendStatements [(statement, values)]).runFrom clock index connection).observation =
      singleObservation (runScriptStep runContext clock index connection statement values).output
        (runScriptStep runContext clock index connection statement values).output := by
  cases step : runScriptStep runContext clock index connection statement values with
  | ended reason => simp [sendStatements, Sql.runFrom, step, SqlRun.observation, singleObservation, RunStep.output,
      Output.endsRun]
  | continued output next others =>
    have quiet := (runScriptStep_continued step).2
    simp [sendStatements, Sql.runFrom, step, SqlRun.observation, singleObservation, RunStep.output, quiet,
      Sql.map]

/-- For every statement, values and inputs, an observation belongs to a branch of the program that sends
the statement exactly when it is {name}`singleObservation` of the step's output with an output that
{name}`OutputChoice` permits. This covers the raw output and every concrete listed rows result. Proof
sketch: a stopping step has one branch; a continuing step selects a permitted output and then
returns the one-output list. -/
theorem sendStatements_single_branch (statement : Syntax.Statement) (values : List Value)
    (clock : Option Clock) (index : Nat) (connection : Connection) (observation : Option (List Output) × List Output) :
    (∃ result, (sendStatements [(statement, values)]).Branch clock index connection result ∧
        result.observation = observation) ↔
      ∃ selected, OutputChoice (runScriptStep runContext clock index connection statement values).output selected ∧
        observation = singleObservation (runScriptStep runContext clock index connection statement values).output
          selected := by
  have program : sendStatements [(statement, values)] = .exec statement values (fun output => .pure [output]) := rfl
  rw [program]
  cases step : runScriptStep runContext clock index connection statement values with
  | ended reason =>
    simp only [RunStep.output]
    constructor
    · rintro ⟨result, branch, rfl⟩
      rw [(Sql.branch_stopped_iff step result).mp branch]
      exact ⟨_, OutputChoice.actual _, rfl⟩
    · rintro ⟨selected, choice, rfl⟩
      have same : selected = .unmodeled reason := by
        rcases choice with rfl | choice
        · rfl
        · exact choice.elim
      subst selected
      exact ⟨_, (Sql.branch_stopped_iff step _).mpr rfl, rfl⟩
  | continued output next others =>
    have quiet := (runScriptStep_continued step).2
    simp only [RunStep.output]
    constructor
    · rintro ⟨result, branch, rfl⟩
      obtain ⟨selected, tail, choice, tailBranch, rfl⟩ := (Sql.branch_continued_iff step result).mp branch
      rw [(Sql.branch_pure_iff _ _ _ _ _).mp tailBranch]
      exact ⟨selected, choice, by simp [singleObservation, quiet, SqlRun.observation]⟩
    · rintro ⟨selected, choice, rfl⟩
      exact ⟨_, (Sql.branch_continued_iff step _).mpr ⟨selected, { outputs := [], connection := next, value := some [selected] },
        choice, .pure _ _ _ _, rfl⟩, by simp [singleObservation, quiet, SqlRun.observation]⟩

/-- For two programs that each send one statement, at any inputs, if the steps have equal outputs then
the actual observations are equal and the sets of branch observations are equal. Proof sketch:
{name}`sendStatements_single_actual` and {name}`sendStatements_single_branch` depend on the step only
through its output. -/
theorem sendStatements_single_observations (first second : Syntax.Statement) (firstValues secondValues : List Value)
    (firstClock secondClock : Option Clock) (firstIndex secondIndex : Nat) (firstConnection secondConnection : Connection)
    (same : (runScriptStep runContext firstClock firstIndex firstConnection first firstValues).output =
      (runScriptStep runContext secondClock secondIndex secondConnection second secondValues).output) :
    ((sendStatements [(first, firstValues)]).runFrom firstClock firstIndex firstConnection).observation =
      ((sendStatements [(second, secondValues)]).runFrom secondClock secondIndex secondConnection).observation ∧
    ∀ observation,
      (∃ result, (sendStatements [(first, firstValues)]).Branch firstClock firstIndex firstConnection result ∧
        result.observation = observation) ↔
      ∃ result, (sendStatements [(second, secondValues)]).Branch secondClock secondIndex secondConnection result ∧
        result.observation = observation := by
  refine ⟨?_, fun observation => ?_⟩
  · rw [sendStatements_single_actual, sendStatements_single_actual, same]
  · rw [sendStatements_single_branch, sendStatements_single_branch, same]

end Belay.Sqlite
