import Belay.Sqlite.Model.ScriptRunAll
import Belay.Sqlite.Model.StatementSingleton
import Belay.Sqlite.Model.StatementExecutionLaws

set_option doc.verso true

/-! The step of a statement that continues (ADR 0019, D4, amended 2026-10-25). Every statement that
the model describes today has one execution, so the complete executions of a script are its one
traversal ({lit}`runScriptAllFrom_eq`). The laws about the traversal then hold for all complete
executions. A statement with more than one execution would end this equality, and the laws would
then need a proof for it. -/

namespace Belay.Sqlite.Model

/-- What a step that continues says about its statement, for every context, optional clock, index,
connection, statement, values, output, connection and list of further executions: if
{name}`runScriptStep` continues with them, then

* the list of further executions is empty, because each statement that the model describes today
  has one next state; only the permitted results of a query ({name}`Output.oneOf`) can be several;
* the statement resolves against the connection to a resolved statement and a resolution state, its
  clock value exists, the connection knows each counter that it reads, and its run passes the support
  check ({name}`StatementRun.ready`);
* the output is the output of its run and its transition ({name}`Output.ofStep`), which does not end the
  run, and the next connection is {name}`Connection.afterStep` of that transition with the counts of the
  run.

Proof sketch: unfold the step along its cases; a restriction, a missing clock value, an unknown counter,
a failed support check and an output {name}`Output.unmodeled` end the run, and the run of the statement
has no alternative ({name}`SqlState.statementRun_alternatives`), so {name}`ranScriptStep` adds no further
execution. -/
theorem runScriptStep_continued_spec {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {next : Connection} {others : List StatementExecution}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    others = [] ∧ ∃ resolved after value,
      resolveStatement context connection.resolveState statement = .ok (resolved, after) ∧
      statementClock clock index resolved = some value ∧
      connection.state.counters.firstUnknown resolved.counterReads = none ∧
      (connection.state.statementRun value parameters resolved).ready = true ∧
      Output.ofStep value parameters resolved connection.state (connection.state.statementRun value parameters resolved)
        (advanceRun index resolved connection.state (connection.state.statementRun value parameters resolved)) = output ∧
      output.endsRun = false ∧
      next = connection.afterStep after (connection.state.statementRun value parameters resolved).counts
        (advanceRun index resolved connection.state (connection.state.statementRun value parameters resolved)) := by
  unfold runScriptStep runScriptStepWith at step
  cases resolution : resolveStatement context connection.resolveState statement with
  | error restriction => simp [resolution] at step
  | ok pair =>
    obtain ⟨resolved, after⟩ := pair
    simp only [resolution] at step
    cases valued : statementClock clock index resolved with
    | none => simp [valued] at step
    | some value =>
      simp only [valued] at step
      cases unknown : connection.state.counters.firstUnknown resolved.counterReads with
      | some kind => simp [unknown] at step
      | none =>
        simp only [unknown] at step
        by_cases ready : (connection.state.statementRun value parameters resolved).ready = true
        · simp only [ready, Bool.not_true, Bool.false_eq_true, ite_false] at step
          unfold ranScriptStep at step
          simp only [StatementExecution.ofAlternatives_of_single, SqlState.statementRun_alternatives, Except.map, List.map_nil] at step
          generalize ofStep : Output.ofStep value parameters resolved connection.state
            (connection.state.statementRun value parameters resolved)
            (advanceRun index resolved connection.state (connection.state.statementRun value parameters resolved)) = produced at step
          cases produced <;> simp [RunStep.withOthers] at step <;>
            (obtain ⟨rfl, rfl, rfl⟩ := step
             exact ⟨rfl, _, _, _, by first | rfl | exact resolution, by first | rfl | exact valued,
               by first | rfl | exact unknown, ready, ofStep, rfl, rfl⟩)
        · simp [ready] at step

/-- For every index, values, connection, resolved statement, resolution state, clock value, run,
transition, output, connection and list of further executions: if the step of a statement that ran
({name}`ranScriptStep`) continues with them, the further executions are the executions of the
alternatives of the run ({name}`StatementExecution.ofAlternatives`). So a user that needs the run and
transition of a further execution reads them there. Proof sketch: unfold the step; an output
{name}`Output.unmodeled` ends the run, and otherwise the step lists the executions of the
alternatives, and ends the run when one has no output. -/
theorem ranScriptStep_continued {index : Nat} {parameters : List Value} {connection : Connection}
    {resolved : Resolved.Statement} {after : ResolveState} {value : Int} {run : StatementRun}
    {transition : SqlTransition} {output : Output} {next : Connection} {others : List StatementExecution}
    (step : ranScriptStep index parameters connection resolved after value run transition =
      .continued output next others) :
    ∃ further, StatementExecution.ofAlternatives index parameters connection resolved after value run = .ok further ∧
      others = further.map StatementExecution.Traced.execution := by
  unfold ranScriptStep at step
  split at step
  · cases step
  all_goals
    cases traced : StatementExecution.ofAlternatives index parameters connection resolved after value run with
    | error reason => simp [traced, RunStep.withOthers, Except.map] at step
    | ok further =>
      simp only [traced, Except.map, RunStep.withOthers] at step
      injection step with _ _ same
      exact ⟨further, rfl, same.symm⟩

/-- For every context, optional clock, index, connection, statement, values, output, connection and
list of further executions: if the step of the statement continues, it has no further execution.
So each statement that the model describes today has one next state. Proof sketch:
{name}`runScriptStep_continued_spec`. -/
theorem runScriptStep_others {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {next : Connection} {others : List StatementExecution}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    others = [] :=
  (runScriptStep_continued_spec step).1

/-- For every step of a statement that continues: its executions are its one execution, the
model's own, with the output and connection of the step. Proof sketch: the other executions are
none ({name}`runScriptStep_others`). -/
theorem runScriptStep_executions {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {next : Connection} {others : List StatementExecution}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    (RunStep.continued output next others).executions = [{ output, next }] := by
  simp [RunStep.executions, runScriptStep_others step]

/-- For every context, optional clock, index, connection and statements with their values, the
complete executions of the script ({name}`runScriptAllFrom`) are the one run of the model's traversal
({name}`runScriptFrom`). So every law about that run holds for every complete execution of the
script. Proof sketch: induction on the statements; the step has no further execution
({name}`runScriptStep_others`), so the executions of the rest start from its one connection. -/
theorem runScriptAllFrom_eq (context : ResolveContext) (clock : Option Clock) :
    ∀ (index : Nat) (connection : Connection) (script : List (Syntax.Statement × List Value)),
      runScriptAllFrom context clock index connection script = [runScriptFrom context clock index connection script]
  | _, _, [] => by simp [runScriptFrom, runScriptAllFrom, runScriptAllWith]
  | index, connection, (statement, parameters) :: rest => by
    unfold runScriptFrom runScriptAllFrom
    cases step : runScriptStep context clock index connection statement parameters with
    | ended reason => simp [runScriptAllWith, step]
    | continued output next others =>
      obtain rfl := runScriptStep_others step
      have := runScriptAllFrom_eq context clock (index + 1) next rest
      simp only [runScriptAllFrom] at this
      simp [runScriptAllWith, step, RunStep.executions, this]

/-- For every context, optional clock, index, connection, statements with their values and
property of runs: if the run of the model's traversal ({name}`runScriptFrom`) has the property, every
complete execution of the script ({name}`runScriptAllFrom`) has it. It is how a law about the
traversal becomes a law about all executions while each statement has one next state. Proof sketch:
the executions are the one traversal ({name}`runScriptAllFrom_eq`). -/
theorem runScriptAllFrom_forall {property : ScriptRun → Prop} (context : ResolveContext) (clock : Option Clock)
    (index : Nat) (connection : Connection) (script : List (Syntax.Statement × List Value))
    (own : property (runScriptFrom context clock index connection script)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, property run := by
  intro run member
  rw [runScriptAllFrom_eq, List.mem_singleton] at member
  exact member ▸ own

end Belay.Sqlite.Model
