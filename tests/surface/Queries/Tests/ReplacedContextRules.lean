import Belay

set_option doc.verso true

/-! Keep both original SELECT context contracts through the final change to their proofs.
The common surface bridge consumes the behavior of the step on the reached connection. -/

namespace Belay.Sqlite.ReplacedContext
open Belay.Sqlite.Model

/-- The former {lit}`check_query_select_at` derives the rows from resolution, clock and readiness. -/
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
  refine Sql.check_query_of_step_rows select head state (property := (· ∈
    bound.possibleResults (state.connection.queryContextAt value parameters query subqueries) source.rows)) ?_ holds
  simp only [runScriptStep_output, resolved]
  rw [resolvedStepOutput_select state.clock state.index _ parameters clocked ready]
  exact (bound.returnsResult_possible _ _ _).2 fun _ member => member

#print axioms check_query_select_at

/-- The former {lit}`check_query_select_faultless` derives readiness from its phase conditions. -/
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

#print axioms check_query_select_faultless

end Belay.Sqlite.ReplacedContext
