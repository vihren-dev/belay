import ReplacedExecutionProjections
import ReplacedNonQueryOutputs
import Belay

set_option doc.verso true

/-! A fixture of {lit}`tests/surface_schema_script_test.py`. The general-send witnesses use the
common rule {name}`Belay.Sqlite.Sql.check_send_of_rule` and the one-execution contract follows from
{name}`Belay.Sqlite.Sql.check_exec`. -/

namespace Belay.Sqlite.ReplacedGeneral
open Belay.Sqlite Model

/-- The former {lit}`Sql.check_send_of_step` contract. Its hypotheses give one execution with
one output, which suffices for the common send rule. -/
theorem Sql.check_send_of_step {ctx : ExecutionContext} {statement : Syntax.Statement} {values : List Value}
    {post : List Output → ExecutionContext → Prop}
    (single : ∀ resolved after, resolveStatement runContext ctx.connection.resolveState statement =
      .ok (resolved, after) → resolved.fromQuery = false)
    (modeled : ∃ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others)
    (notChoice : ∀ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others →
        ∀ alternatives, output ≠ .oneOf alternatives)
    (reached : ∀ output next,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next [] →
        next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next))
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  obtain ⟨output, next, others, step⟩ := modeled
  obtain rfl := runScriptStep_others_of_single step single
  refine Sql.check_send_of_rule step valid rfl ?_
  intro execution member held
  obtain rfl : execution = ⟨output, next⟩ := by simpa [RunStep.executions] using member
  refine ⟨reached _ _ step held, ?_⟩
  cases output with
  | oneOf rows => exact (notChoice _ _ _ step rows rfl).elim
  | done _ | rows _ | error _ | unmodeled _ => trivial

#print axioms Sql.check_send_of_step

/-- The former {lit}`Sql.check_send_of_step_notInsertSelect` contract. The syntax hypothesis
implies that resolution gives a single execution. -/
theorem Sql.check_send_of_step_notInsertSelect {ctx : ExecutionContext} {statement : Syntax.Statement}
    {values : List Value} {post : List Output → ExecutionContext → Prop}
    (notInsertSelect : statement.isInsertSelect = false)
    (modeled : ∃ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others)
    (notChoice : ∀ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others →
        ∀ alternatives, output ≠ .oneOf alternatives)
    (reached : ∀ output next,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next [] →
        next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next))
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned)) :
    (send ⟨[(statement, values)]⟩).check post ctx :=
  Sql.check_send_of_step (fun _ _ found => resolveStatement_single _ _ _ _ _ notInsertSelect found)
    modeled notChoice reached valid

#print axioms Sql.check_send_of_step_notInsertSelect

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
