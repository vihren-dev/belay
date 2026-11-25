import Belay

set_option doc.verso true

/-! The validity-free, two-way check of a one-statement send remains a trust witness. -/

namespace Belay.Sqlite.ReplacedGeneral
open Model

/-- For every post, context, statement, values and continuing step whose output is not a choice and
whose statement resolves to no INSERT from a query without rules: a program that sends the one statement
checks the post exactly at the context after the step with the one output. Proof sketch:
{name}`Sql.check_exec` with the step; the resolver witness and {name}`runScriptStep_others` rule out further executions and
the output is not a choice, so only the raw continuation remains. -/
theorem check_send_single_of_step {statement : Syntax.Statement} {values : List Value}
    {post : List Output → ExecutionContext → Prop} {state : ExecutionContext}
    {actual : Output} {connection : Connection} {others : List StatementExecution}
    (step : runScriptStep runContext state.clock state.index state.connection statement values =
      .continued actual connection others)
    (single : ∀ resolved after, resolveStatement runContext state.connection.resolveState statement =
      .ok (resolved, after) → resolved.fromQuery = false)
    (notChoice : ∀ alternatives, actual ≠ .oneOf alternatives) :
    (send ⟨[(statement, values)]⟩).check post state ↔ post [actual] (state.next actual connection) := by
  unfold send
  simp only [sendStatements]
  rw [Sql.check_exec, step]
  dsimp only
  obtain ⟨resolved, after, _, found, _⟩ := runScriptStep_execution_runs step
  obtain rfl := runScriptStep_others step found (single resolved after found)
  simp only [RunStep.executions]
  simp only [List.mem_singleton, forall_eq]
  cases actual with
  | oneOf alternatives => exact absurd rfl (notChoice alternatives)
  | done _ | rows _ | error _ | unmodeled _ =>
    simp [Sql.check_pure, Sql.map]

#print axioms check_send_single_of_step

end Belay.Sqlite.ReplacedGeneral
