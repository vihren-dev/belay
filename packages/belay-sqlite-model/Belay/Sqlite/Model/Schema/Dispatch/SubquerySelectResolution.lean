import Belay.Sqlite.Model.Queries.Select.SimpleStatementResolution
import Belay.Sqlite.Model.Schema.Dispatch.SimpleStatementResolution
import Belay.Sqlite.Model.Queries.Select.SubqueryExprResolutionLaws

set_option doc.verso true

/-! The resolution of a {lit}`SELECT` without {lit}`FROM` and with one subquery (ADR 0017, S4):
the statement {lit}`SELECT e WHERE c(q)` where {lit}`c` names the subquery {lit}`q` once or more. The
subquery is resolved first, in the scope of its own sources, and the shapes of the result give the
resolution of the statement's own query. The lemma takes both resolutions as hypotheses, because
the catalog is free: a proof of a claim over every database gives them from the table that the
subquery names. -/

namespace Belay.Sqlite.Model

/-- For every {lit}`SELECT` statement of an ordinary query without parent or WITH declaration and a list of subqueries, whose resolution of
the query with the subqueries against the catalog of the state gives a resolved statement and
the same catalog, the resolution of the statement gives that statement and leaves the state as it is.
Proof sketch: the statement builds the query from its clauses, and the resolution of the
statement is that of the query. -/
theorem resolveStatement_select_of_resolveSelect (context : ResolveContext) (state : ResolveState)
    (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) (parent : query.parent = none)
    (ordinary : query.commonTable = none) (statement : Resolved.Statement)
    (resolved : resolveSelect context state.catalog query subqueries = .ok (statement, state.catalog)) :
    resolveStatement context state (.select query.columns query.source query.joins query.filter query.groupBy
        query.orderBy query.limit query.offset subqueries query.having query.distinct query.compound) =
      .ok (statement, state) := by
  have rebuilt : ({ query with parent := none, commonTable := none } : Syntax.Subquery) = query := by
    cases query
    simp_all
  have unfolded : resolveStatement context state (.select query.columns query.source query.joins query.filter
      query.groupBy query.orderBy query.limit query.offset subqueries query.having query.distinct query.compound) =
      state.withCatalog (resolveSelect context state.catalog { query with parent := none, commonTable := none } subqueries) := rfl
  rw [unfolded, rebuilt, resolved]
  rfl

end Belay.Sqlite.Model
