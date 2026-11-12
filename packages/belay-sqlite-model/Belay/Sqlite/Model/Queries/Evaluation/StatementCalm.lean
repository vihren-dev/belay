import Belay.Sqlite.Model.Shared.Execution.StatementCounterReads
import Belay.Sqlite.Model.Queries.Evaluation.StatementClock

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- A calm expression: none of its parts is a fallible call ({name}`Expr.isFallibleCall`), a read
of the clock ({name}`Expr.readsClockHere`) or a call of a counter function
({name}`Expr.readsCounterHere`). For example, a comparison of a column with a literal is calm, and
{lit}`abs(x)` is not, because {lit}`abs` can fail. -/
def Expr.Calm (expression : Expr) : Prop :=
  expression.any Expr.isFallibleCall = false ∧ expression.any Expr.readsClockHere = false ∧
    ∀ kind, expression.any (Expr.readsCounterHere kind) = false

/-- A calm statement: every expression that its evaluation reads is calm
({name}`Expr.Calm`, {name}`Statement.clockExpressions`). A statement without expressions is calm. -/
def Statement.Calm (statement : Statement) : Prop :=
  ∀ expression ∈ statement.clockExpressions, expression.Calm

/-- For every calm statement of a query with subqueries, the expressions of the query have no
fallible call. Proof sketch: the expressions of the query are among those of the statement. -/
theorem Statement.Calm.query_plain {query : Query} {subqueries : List Query} (calm : (Statement.query query subqueries).Calm) :
    query.expressions.all (!·.any Expr.isFallibleCall) = true := by
  simp only [List.all_eq_true, Bool.not_eq_true']
  exact fun expression member => (calm expression (by simp [Statement.clockExpressions, member])).1

/-- For every calm statement of a query with subqueries, the expressions of each subquery have no
fallible call. Proof sketch: the expressions of a subquery are among those of the statement
({name}`Statement.clockExpressions`). -/
theorem Statement.Calm.subquery_plain {query : Query} {subqueries : List Query}
    (calm : (Statement.query query subqueries).Calm) {inner : Query} (member : inner ∈ subqueries) :
    inner.expressions.all (!·.any Expr.isFallibleCall) = true := by
  simp only [List.all_eq_true, Bool.not_eq_true']
  intro expression inside
  have present : expression ∈ (Statement.query query subqueries).clockExpressions := by
    simp only [Statement.clockExpressions, List.mem_append, List.mem_flatMap]
    exact .inr ⟨inner, member, inside⟩
  exact (calm expression present).1

/-- For every calm statement of a query with subqueries, the model's check of the subqueries
({name}`subqueriesPlain`) passes for the subqueries that are no term of a compound. Proof sketch:
the nested subqueries are among the subqueries of the statement, whose expressions are calm
({name}`Statement.Calm.subquery_plain`). -/
theorem Statement.Calm.subqueries_plain {query : Query} {subqueries : List Query}
    (calm : (Statement.query query subqueries).Calm) : subqueriesPlain (query.nestedSubqueries subqueries) = true := by
  have each : ∀ inner ∈ subqueries, inner.expressions.all (!·.any Expr.isFallibleCall) = true :=
    fun inner member => calm.subquery_plain member
  unfold Query.nestedSubqueries
  split
  · exact List.all_eq_true.mpr each
  · exact List.all_eq_true.mpr fun inner member => each inner (by
      obtain ⟨⟨_, index⟩, kept, rfl⟩ := List.mem_map.mp member
      exact List.fst_mem_of_mem_zipIdx (List.mem_filter.mp kept).1)

end Belay.Sqlite.Model.Resolved
