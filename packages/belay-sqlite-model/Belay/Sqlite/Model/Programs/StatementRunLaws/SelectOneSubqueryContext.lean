import Belay.Sqlite.Model.Programs.StatementRunLaws.SelectCalmRule
import Belay.Sqlite.Model.Schema.Dispatch.TableSourceLaws
import Belay.Sqlite.Model.Queries.Evaluation.ExprEvalLaws
import Belay.Sqlite.Model.Queries.Evaluation.ExprCalmLaws
import Belay.Sqlite.Model.Queries.Evaluation.CountOf

set_option doc.verso true

/-! The context of a statement with one subquery (ADR 0017, S4): for a calm statement, subquery 0
of its context is the run of the subquery in the context of the values. The statement
{lit}`SELECT 1 WHERE c` with the one subquery {lit}`SELECT e FROM t WHERE p` is calm when {lit}`c`,
{lit}`p` and {lit}`e` are calm, and quiet when they are quiet; with the count query {lit}`SELECT count(*) FROM t WHERE p` as its subquery, it is
calm when both conditions are calm. -/

namespace Belay.Sqlite.Model

/-- For every connection, values, query and calm statement of the query with one subquery, subquery 0 of the context
of the statement on the connection, for an outer row, is the run of that subquery
({name}`Resolved.Query.subqueryRun`) in the context of the values, over the database of the connection. Proof
sketch: the statement reads no counter, so its context is the context of the values with the
subquery list at depth one, and the definition of {name}`Resolved.subqueryContext` computes. -/
theorem Connection.queryContext_subquery_zero (connection : Connection) (parameters : List Value)
    (query inner : Resolved.Query) (calm : (Resolved.Statement.query query [inner]).Calm) (outer : List Value) :
    (connection.queryContext parameters query [inner]).subqueries 0 outer =
      inner.subqueryRun (Resolved.EvalContext.bound parameters) connection.state.database outer := by
  simp only [Connection.queryContext, calm.counterReads, Resolved.statementContext]
  rfl

end Belay.Sqlite.Model
