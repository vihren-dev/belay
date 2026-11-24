import Belay.Sqlite.Programs.Reasoning.ExecutionSuccess

set_option doc.verso true

/-!
The check of a program that sends one statement whose step continues with one execution (ADR 0017, S6): the
check is the post at the context after the step. The fresh-send rules and the
fresh-run rules of UPDATE, DELETE and ADD COLUMN build on it.
-/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every post, context, statement, values and continuing step whose output is not a choice and
whose statement resolves to no INSERT from a query without rules: a program that sends the one statement
checks the post exactly at the context after the step with the one output. Proof sketch:
{name}`Sql.check_exec` with the step; the step has one execution ({name}`runScriptStep_executions`) and
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
  rw [runScriptStep_executions step single]
  simp only [List.mem_singleton, forall_eq]
  cases actual with
  | oneOf alternatives => exact absurd rfl (notChoice alternatives)
  | done _ | rows _ | error _ | unmodeled _ =>
    simp [Sql.check_pure, Sql.map]

end Belay.Sqlite
