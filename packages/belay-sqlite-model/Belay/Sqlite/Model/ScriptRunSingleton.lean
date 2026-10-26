import Belay.Sqlite.Model.ScriptRunContinued

set_option doc.verso true

/-! The executions of the steps of a script (ADR 0019, D4, amended 2026-10-25), from the step theorems of
{lit}`ScriptRunContinued`. Every statement that
the model describes has one execution, except INSERT from a query without rules
({lit}`Resolved.Statement.fromQuery`), which can have several. For a script whose statements all have
one execution, the complete executions of the script are its one traversal ({lit}`runScriptAllFrom_eq`).
A law that must hold for every statement quantifies over all executions of each step instead
({lit}`runScriptStep_execution_runs`). -/

namespace Belay.Sqlite.Model

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
