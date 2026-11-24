import Belay

set_option doc.verso true

/-! The former singleton and SELECT projections follow from the execution list and SELECT frame. -/

namespace Belay.Sqlite.Model

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

/-- Recover the former successful SELECT connection projection. -/
theorem runScriptStep_select_connection {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {columns source joins filter groupBy orderBy limit offset subqueries having
      distinct compound parameters output} {others : List StatementExecution}
    (step : runScriptStep context clock index connection
      (.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
      parameters = .continued output next others)
    (noError : output.isError = false) : next = connection :=
  (runScriptStep_select_keeps step).2

/-- Recover the former SELECT execution-list projection. -/
theorem runScriptStep_select_others {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {columns source joins filter groupBy orderBy limit offset subqueries having distinct compound}
    (isSelect : statement =
      .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
    {output : Output} {next : Connection} {others : List StatementExecution}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    others = [] := by
  subst isSelect
  exact (runScriptStep_select_keeps step).1

#print axioms runScriptStep_executions
#print axioms runScriptStep_others_of_single
#print axioms runScriptStep_select_connection
#print axioms runScriptStep_select_others

end Belay.Sqlite.Model
