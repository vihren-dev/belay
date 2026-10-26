import Belay.Sqlite.Model.ScriptRunAll
import Belay.Sqlite.Model.ScriptConditions
import Belay.Sqlite.Model.StatementSingleton
import Belay.Sqlite.Model.StatementExecutionLaws

set_option doc.verso true

/-! The step of a statement that continues (ADR 0019, D4, amended 2026-10-25). Every statement that
the model describes has one execution, except INSERT from a query without rules
({lit}`Resolved.Statement.fromQuery`), which can have several. For a script whose statements all have
one execution, the complete executions of the script are its one traversal ({lit}`runScriptAllFrom_eq`).
A law that must hold for every statement quantifies over all executions of each step instead
({lit}`runScriptStep_execution_runs`). -/

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

/-- For every step of a statement that continues: none of its executions has an output that ends the run
({name}`Output.endsRun`). So every execution of a step leaves a modeled output, which a later statement
continues from. Proof sketch: the model's own output continues the run ({name}`runScriptStep_continued_spec`),
and so does the output of each further execution ({name}`StatementExecution.ofAlternatives_continues`). -/
theorem runScriptStep_executions_continue {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {next : Connection} {others : List StatementExecution}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    ∀ execution ∈ (RunStep.continued output next others).executions, execution.output.endsRun = false := by
  obtain ⟨resolved, after, value, _, _, _, _, _, endsRun, _, further, listed, rfl⟩ :=
    runScriptStep_continued_spec step
  intro execution member
  simp only [RunStep.executions, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨traced, inFurther, rfl⟩
  · exact endsRun
  · exact StatementExecution.ofAlternatives_continues listed traced inFurther

/-- For every step of a statement that continues, when every statement that it resolves to is no INSERT from a
query without rules: its executions are its one execution, the model's own, with the output and
connection of the step. Proof sketch: the other executions are none ({name}`runScriptStep_others`). -/
theorem runScriptStep_executions {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {next : Connection} {others : List StatementExecution}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (single : ∀ resolved after, resolveStatement context connection.resolveState statement = .ok (resolved, after) →
      resolved.fromQuery = false) :
    (RunStep.continued output next others).executions = [{ output, next }] := by
  obtain ⟨resolved, after, _, found, _⟩ := runScriptStep_execution_runs step
  simp [RunStep.executions, runScriptStep_others step found (single resolved after found)]

/-- For every context, optional clock, index, connection and statements with their values, when each
statement that the run reaches resolves to a statement that is no INSERT from a query without rules
({name}`ScriptConditionsWith` for the condition {lit}`fromQuery = false`), the complete executions of the
script ({name}`runScriptAllFrom`) are the one run of the model's traversal ({name}`runScriptFrom`). So every
law about that run holds for every complete execution of the script. Proof sketch: induction on the
statements; the step has no further execution ({name}`runScriptStep_others`), so the executions of the rest
start from its one connection. -/
theorem runScriptAllFrom_eq (context : ResolveContext) (clock : Option Clock) :
    ∀ (index : Nat) (connection : Connection) (script : List (Syntax.Statement × List Value)),
      ScriptConditionsWith (fun resolved _ => resolved.fromQuery = false) context clock index connection script →
        runScriptAllFrom context clock index connection script = [runScriptFrom context clock index connection script]
  | _, _, [], _ => by simp [runScriptFrom, runScriptAllFrom, runScriptAllWith]
  | index, connection, (statement, parameters) :: rest, single => by
    unfold runScriptFrom runScriptAllFrom
    cases step : runScriptStep context clock index connection statement parameters with
    | ended reason => simp [runScriptAllWith, step]
    | continued output next others =>
      simp only [ScriptConditionsWith, step] at single
      obtain ⟨found, later⟩ := single
      obtain ⟨resolved, after, _, resolution, _⟩ := runScriptStep_execution_runs step
      obtain rfl := runScriptStep_others step resolution (found resolved after resolution)
      have := runScriptAllFrom_eq context clock (index + 1) next rest (later { output, next } (by simp [RunStep.executions]))
      simp only [runScriptAllFrom] at this
      simp [runScriptAllWith, step, RunStep.executions, this]

/-- For every step of a statement that continues, when every statement that it resolves to is no INSERT from a
query without rules ({name}`Resolved.Statement.fromQuery`): the step has no further execution. Proof sketch:
{name}`runScriptStep_execution_runs` gives the resolution of the statement and {name}`runScriptStep_others`
the claim. -/
theorem runScriptStep_others_of_single {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {next : Connection} {others : List StatementExecution}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (single : ∀ resolved after, resolveStatement context connection.resolveState statement = .ok (resolved, after) →
      resolved.fromQuery = false) : others = [] := by
  obtain ⟨resolved, after, _, found, _⟩ := runScriptStep_execution_runs step
  exact runScriptStep_others step found (single resolved after found)

/-- For every condition that statements are no INSERT from a query without rules
({name}`ScriptConditionsWith` for {lit}`fromQuery = false`), and every step of its first statement that
continues: the step has no further execution, and the condition holds for the rest from the next index
and the next connection. Proof sketch: the first statement resolves to a statement that is no INSERT from
a query ({name}`runScriptStep_execution_runs`), so {name}`runScriptStep_others` applies; the condition of the
rest is asked for the one execution. -/
theorem ScriptConditionsWith.single_step {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {rest : List (Syntax.Statement × List Value)} {output : Output} {next : Connection}
    {others : List StatementExecution}
    (single : ScriptConditionsWith (fun resolved _ => resolved.fromQuery = false) context clock index connection
      ((statement, parameters) :: rest))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    others = [] ∧ ScriptConditionsWith (fun resolved _ => resolved.fromQuery = false) context clock (index + 1) next rest := by
  simp only [ScriptConditionsWith, step] at single
  obtain ⟨found, later⟩ := single
  obtain ⟨resolved, after, _, resolution, _⟩ := runScriptStep_execution_runs step
  obtain rfl := runScriptStep_others step resolution (found resolved after resolution)
  exact ⟨rfl, later { output, next } (by simp [RunStep.executions])⟩

end Belay.Sqlite.Model
