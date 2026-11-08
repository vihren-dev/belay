import Belay.Sqlite.ReadStepRule
import Belay.Sqlite.SelectResultBridge

set_option doc.verso true

/-! The execution rules of a SELECT at a reached context (ADR 0027, D5): a SELECT after other
statements reads the clock, the statement index and the connection of the context that those
statements reached, not those of the start. The rules take the readiness premises
({lit}`Belay.Sqlite.Model.Connection.SelectReady`) at that context, so a query that reads the clock
or a counter states its premises about that context explicitly. A SELECT keeps the connection, so
the rules also give that the context after the SELECT has the connection of the context before
it. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- Context rule: for every script of one SELECT ({name}`Script.isSelect`) with its values, proof
that it has one statement, context {lit}`state`, clock value {lit}`value`, source rows
{lit}`source`, query {lit}`bound` and post {lit}`P`: when

* the statement resolves on the connection of {lit}`state` to a query with subqueries,
* the statement reads the clock value {lit}`value` at the clock and the index of {lit}`state`
  ({name}`statementClock`),
* the connection of {lit}`state` is ready for the query with {lit}`value`, the values,
  {lit}`source` and {lit}`bound` ({name}`Connection.SelectReady`), and
* for every result that the model permits for {lit}`bound` over the source rows in the query
  context of that connection, {lit}`P` holds for the result and every context whose connection is
  the connection of {lit}`state`,

then the program {name}`query` of the script checks {lit}`P` at {lit}`state`. The premises read
the context of {lit}`state` and not of a run from the start. Proof sketch:
{name}`runScriptStep_select_returnsResult` gives a step that continues and whose output returns
one of the permitted results; {name}`Sql.check_query_select` reads the step and keeps the
connection. -/
theorem check_query_select_at {script : Script} {one : script.statements.length = 1}
    {statement : Syntax.Statement} {parameters : List Value} (select : script.isSelect = true)
    (head : script.statements = [(statement, parameters)]) (state : ExecutionContext) {query bound : Resolved.Query}
    {subqueries : List Resolved.Query} {after : ResolveState} {value : Int} {source : Resolved.SourceRows}
    (resolved : resolveStatement runContext state.connection.resolveState statement = .ok (.query query subqueries, after))
    (clocked : statementClock state.clock state.index (.query query subqueries) = some value)
    (ready : state.connection.SelectReady value parameters query subqueries source bound)
    (post : Except Nat (List (List Value)) → ExecutionContext → Prop)
    (holds : ∀ result ∈ bound.possibleResults (state.connection.queryContextAt value parameters query subqueries)
      source.rows, ∀ final : ExecutionContext, final.connection = state.connection → post (.ok result) final) :
    (Belay.Sqlite.query script one).check post state := by
  obtain ⟨values, columns, from_, joins, filter, groupBy, orderBy, limit, offset, nested, having, distinct, compound,
    same⟩ := Script.select_shape select
  obtain ⟨rfl, rfl⟩ : statement = .select columns from_ joins filter groupBy orderBy limit offset nested having
      distinct compound ∧ parameters = values := by simpa [head] using same
  have returns := (runScriptStep_select_returnsResult runContext state.clock state.index state.connection _ _
    resolved clocked ready (· ∈ bound.possibleResults (state.connection.queryContextAt value parameters query subqueries)
      source.rows)).2 fun _ member => member
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

/-- Calm context rule: {name}`check_query_select_at` for a calm query
({name}`Resolved.Statement.Calm`) that is no compound. For every script of one SELECT with its
values, context {lit}`state`, source rows {lit}`source`, query {lit}`bound` and post {lit}`P`:
when the statement resolves on the connection of {lit}`state`, the query's sources give
{lit}`source` over the database of that connection in the statement context
({name}`Resolved.EvalContext.statement`), {lit}`source` has no possible fault, the window binds to
{lit}`bound`, each expression of the query has no fault over the empty row and over each source
row, {lit}`bound` has no overflow and a certain {lit}`DISTINCT`, and {lit}`P` holds for every
permitted result in the statement context and every context with the connection of {lit}`state`,
then the program {name}`query` of the script checks {lit}`P` at {lit}`state`. The clock, the
index and the counters of {lit}`state` do not matter; its database does. Proof sketch:
{name}`Connection.SelectReady.of_faultless` and {name}`Connection.queryContext_calm`. -/
theorem check_query_select_faultless {script : Script} {one : script.statements.length = 1}
    {statement : Syntax.Statement} {parameters : List Value} (select : script.isSelect = true)
    (head : script.statements = [(statement, parameters)]) (state : ExecutionContext) {query bound : Resolved.Query}
    {subqueries : List Resolved.Query} {after : ResolveState} {source : Resolved.SourceRows}
    (resolved : resolveStatement runContext state.connection.resolveState statement = .ok (.query query subqueries, after))
    (calm : (Resolved.Statement.query query subqueries).Calm) (single : query.compound = none)
    (found : query.source (Resolved.EvalContext.statement parameters state.connection.state.database subqueries)
      state.connection.state.database = some source)
    (sourceCertain : source.fault ≠ .may) (window : query.bindWindow parameters = some bound)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate (Resolved.EvalContext.statement parameters state.connection.state.database subqueries)
        row).2 = .none)
    (noOverflow : bound.fails (Resolved.EvalContext.statement parameters state.connection.state.database subqueries)
      source.rows = false)
    (distinct : bound.distinctCertain
      (Resolved.EvalContext.statement parameters state.connection.state.database subqueries) source.rows = true)
    (post : Except Nat (List (List Value)) → ExecutionContext → Prop)
    (holds : ∀ result ∈ bound.possibleResults
        (Resolved.EvalContext.statement parameters state.connection.state.database subqueries) source.rows,
      ∀ final : ExecutionContext, final.connection = state.connection → post (.ok result) final) :
    (Belay.Sqlite.query script one).check post state := by
  refine check_query_select_at select head state resolved (by simp [statementClock, calm.readsClock])
    (Connection.SelectReady.of_faultless state.connection parameters calm single window found sourceCertain faultless
      noOverflow distinct) post ?_
  have context : state.connection.queryContextAt 0 parameters query subqueries =
      Resolved.EvalContext.statement parameters state.connection.state.database subqueries :=
    Connection.queryContext_calm _ parameters query subqueries calm
  rw [context]
  exact holds

end Belay.Sqlite
