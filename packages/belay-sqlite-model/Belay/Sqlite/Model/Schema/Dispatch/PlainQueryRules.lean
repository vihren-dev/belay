import Belay.Sqlite.Model.Queries.Evaluation.SelectWindowRules
import Belay.Sqlite.Model.Queries.Evaluation.QueryPlainLaws
import Belay.Sqlite.Model.Schema.Dispatch.Subqueries

set_option doc.verso true

/-! The plain query value and the rules of a query without {lit}`ORDER BY` and window (ADR 0027,
D1). {lit}`Query.simple` builds the query of a read without aggregation, grouping, ordering,
window, {lit}`HAVING`, {lit}`DISTINCT` or compound. The rules hold for every query with the
named fields: a query without a sort term has one tie group, so the model permits one result,
and a window without {lit}`OFFSET` and {lit}`LIMIT` cuts nowhere. -/

namespace Belay.Sqlite.Model.Resolved

/-- Outer source rule: for every context, database, optional initial database and query that
reads no cell of an outer query, the source rows after the empty outer row
({name}`Query.sourceAfter`) are the source rows of the query ({name}`Query.source`). Proof sketch:
both fold the sources over the one row with no cells. -/
theorem Query.sourceAfter_of_outer_zero (context : EvalContext) (database : Database) (initial : Option Database)
    {query : Query} (outer : query.outer = 0) :
    query.sourceAfter context [] database initial = query.source context database initial := by
  simp [Query.sourceAfter, outer, Query.source]

end Belay.Sqlite.Model.Resolved
