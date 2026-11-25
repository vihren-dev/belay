import Belay.Sqlite.Programs.Claims.ReadStepRule
import Belay.Sqlite.Programs.Claims.SelectResultBridge

set_option doc.verso true

/-! A check of a SELECT at a reached context can use any property of the rows returned
by its modeled step. This applies after earlier statements and across result choices. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every one-statement script, statement, parameter values, starting context, row
property and postcondition, {name}`query` checks the postcondition at that context if:
* {name}`Script.isSelect` holds and the script consists of that statement with those values;
* the output of {name}`runScriptStep` at the starting clock, index and connection satisfies
  {name}`Output.returnsResult` for the property (every choice returns rows with the property);
* for every row list satisfying the property, including lists outside the actual outputs,
  the postcondition holds for its successful result at every context with the starting connection.

An error requires no postcondition proof because the output premise excludes it. Proof sketch:
apply {name}`Sql.check_query_select` and {name}`OutputChoice.forall_queryResult_iff`. -/
theorem Sql.check_query_of_step_rows {script : Script} {one : script.statements.length = 1}
    {statement : Syntax.Statement} {parameters : List Value} (select : script.isSelect = true)
    (head : script.statements = [(statement, parameters)]) (state : ExecutionContext)
    {property : List (List Value) → Prop}
    (returns : (runScriptStep runContext state.clock state.index state.connection statement parameters).output.returnsResult property)
    {post : Except Nat (List (List Value)) → ExecutionContext → Prop}
    (holds : ∀ rows, property rows → ∀ final : ExecutionContext, final.connection = state.connection →
      post (.ok rows) final) : (query script one).check post state := by
  obtain ⟨values, columns, from_, joins, filter, groupBy, orderBy, limit, offset, nested, having, distinct, compound,
    same⟩ := Script.select_shape select
  obtain ⟨rfl, rfl⟩ : statement = .select columns from_ joins filter groupBy orderBy limit offset nested having
      distinct compound ∧ parameters = values := by simpa [head] using same
  cases step : runScriptStep runContext state.clock state.index state.connection
      (.select columns from_ joins filter groupBy orderBy limit offset nested having distinct compound) parameters with
  | ended reason =>
    rw [step] at returns
    simp [RunStep.output, Output.returnsResult] at returns
  | continued output next others =>
    refine Sql.check_query_select head rfl ⟨output, next, others, step⟩ fun selected choice => ?_
    rw [step] at returns choice
    have each := (OutputChoice.forall_queryResult_iff (runScriptStep_select_output step) _).2 returns selected choice
    revert each
    cases queryResult selected with
    | ok rows => exact fun member => holds rows member _ rfl
    | error _ => exact False.elim

end Belay.Sqlite
