import Belay.Sqlite.Model.ScriptRunAll
import Belay.Sqlite.Model.ScriptConditions
import Belay.Sqlite.Model.StatementSingleton
import Belay.Sqlite.Model.StatementExecutionLaws

set_option doc.verso true

/-! The step of a statement that continues (ADR 0019, D4, amended 2026-10-25): what a step that continues says
about its statement, its output, its next connection and its further executions. The consequences for the executions
of a whole script are in {lit}`Belay.Sqlite.Model.ScriptRunSingleton`. -/

namespace Belay.Sqlite.Model

/-- What a step that continues says about its statement, for every context, optional clock, index,
connection, statement, values, output, connection and list of further executions: if
{name}`runScriptStep` continues with them, then

* the statement resolves against the connection to a resolved statement and a resolution state, its
  clock value exists, the connection knows each counter that it reads, and its run passes the support
  check ({name}`StatementRun.ready`);
* the output is the output of its run and its transition ({name}`Output.ofStep`), which does not end the
  run, and the next connection is {name}`Connection.afterStep` of that transition with the counts of the
  run;
* the further executions are those of the alternatives of the run
  ({name}`StatementExecution.ofAlternatives`).

Proof sketch: unfold the step along its cases; a restriction, a missing clock value, an unknown counter,
a failed support check and an output {name}`Output.unmodeled` end the run, and an alternative without
an output ends it too. -/
theorem runScriptStep_continued_spec {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {next : Connection} {others : List StatementExecution}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    ∃ resolved after value,
      resolveStatement context connection.resolveState statement = .ok (resolved, after) ∧
      statementClock clock index resolved = some value ∧
      connection.state.counters.firstUnknown resolved.counterReads = none ∧
      (connection.state.statementRun value parameters resolved).ready = true ∧
      Output.ofStep value parameters resolved connection.state (connection.state.statementRun value parameters resolved)
        (advanceRun index resolved connection.state (connection.state.statementRun value parameters resolved)) = output ∧
      output.endsRun = false ∧
      next = connection.afterStep after (connection.state.statementRun value parameters resolved).counts
        (advanceRun index resolved connection.state (connection.state.statementRun value parameters resolved)) ∧
      ∃ further, StatementExecution.ofAlternatives index parameters connection resolved after value
          (connection.state.statementRun value parameters resolved) = .ok further ∧
        others = further.map StatementExecution.Traced.execution := by
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
          generalize ofStep : Output.ofStep value parameters resolved connection.state
            (connection.state.statementRun value parameters resolved)
            (advanceRun index resolved connection.state (connection.state.statementRun value parameters resolved)) = produced at step
          cases traced : StatementExecution.ofAlternatives index parameters connection resolved after value
              (connection.state.statementRun value parameters resolved) with
          | error reason => cases produced <;> simp [RunStep.withOthers, traced, Except.map] at step
          | ok further =>
            cases produced <;> simp [RunStep.withOthers, traced, Except.map] at step <;>
              (obtain ⟨rfl, rfl, rfl⟩ := step
               exact ⟨_, _, _, by first | rfl | exact resolution, by first | rfl | exact valued,
                 by first | rfl | exact unknown, ready, ofStep, rfl, rfl, further, traced, rfl⟩)
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

/-- For every context, optional clock, index, connection, statement, values, output, connection, list of
further executions, resolved statement and resolution state: if the step of the statement continues and the
statement resolves to a statement that is no INSERT from a query without rules
({name}`Resolved.Statement.fromQuery`), the step has no further execution. So such a statement has one
next state. Proof sketch: {name}`runScriptStep_continued_spec` gives the further executions as those of the
alternatives of the run, and the run has none ({name}`SqlState.statementRun_alternatives`). -/
theorem runScriptStep_others {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {next : Connection} {others : List StatementExecution} {resolved : Resolved.Statement} {after : ResolveState}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (resolution : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (single : resolved.fromQuery = false) : others = [] := by
  obtain ⟨resolved', after', value, found, _, _, _, _, _, _, further, listed, same⟩ := runScriptStep_continued_spec step
  rw [resolution] at found
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj found).symm
  rw [StatementExecution.ofAlternatives_of_single index parameters connection resolved' after' value
    (SqlState.statementRun_alternatives _ _ _ _ _ single)] at listed
  cases listed
  simpa using same

/-- For every step of a statement that continues, and every execution of the step
({name}`RunStep.executions`): the statement resolves, its run passes the support check, and the next
connection of the execution is the connection after the transition of some run
({name}`Connection.afterStep`, {name}`advanceRun`), whose effect is the effect of an admitted execution of
the statement ({name}`StatementRun.effects`). So a law about the effect of every admitted execution of a
statement is a law about the next connection of every execution of its step. Proof sketch: the model's own
execution is the run of the statement ({name}`runScriptStep_continued_spec`); a further execution comes from an
alternative of the run ({name}`StatementExecution.ofAlternatives_mem`), whose run has the effect of the
alternative. -/
theorem runScriptStep_execution_runs {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {next : Connection} {others : List StatementExecution}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    ∃ resolved after value,
      resolveStatement context connection.resolveState statement = .ok (resolved, after) ∧
      (connection.state.statementRun value parameters resolved).ready = true ∧
      ∀ execution ∈ (RunStep.continued output next others).executions,
        ∃ run : StatementRun, run.effect ∈ (connection.state.statementRun value parameters resolved).effects ∧
          execution.next = connection.afterStep after run.counts (advanceRun index resolved connection.state run) := by
  obtain ⟨resolved, after, value, found, _, _, ready, _, _, nextEq, further, listed, rfl⟩ := runScriptStep_continued_spec step
  refine ⟨resolved, after, value, found, ready, ?_⟩
  intro execution member
  simp only [RunStep.executions, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨traced, inFurther, rfl⟩
  · exact ⟨_, StatementRun.effect_mem_effects _, nextEq⟩
  · obtain ⟨alternative, inAlternatives, _, transitionEq, nextAlternative⟩ :=
      StatementExecution.ofAlternatives_mem listed traced inFurther
    exact ⟨alternative.toRun, List.mem_cons_of_mem _ (List.mem_map_of_mem inAlternatives),
      by rw [nextAlternative, transitionEq]; rfl⟩

end Belay.Sqlite.Model
