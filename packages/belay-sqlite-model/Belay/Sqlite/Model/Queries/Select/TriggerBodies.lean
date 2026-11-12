import Belay.Sqlite.Model.Queries.Preparation.CommonTableWrites
import Belay.Sqlite.Model.Queries.Select.TriggerRaise
import Belay.Sqlite.Model.Queries.Evaluation.StatementClock

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whether a query of a raising SELECT is one that the model evaluates: no source, no
aggregate, no grouping, order, window, {lit}`HAVING` or {lit}`DISTINCT`, no subquery and no call
that can fail, so its one row raises in a known order. -/
def raiseQueryPlain (query : Resolved.Query) (subqueries : List Resolved.Query) : Bool :=
  query.sources.isEmpty && !query.aggregate && query.groupBy.isEmpty && query.orderBy.isEmpty && query.limit.isNone &&
    query.offset == 0 && query.having.isNone && query.distinct.isNone && subqueries.isEmpty &&
    !query.expressions.any (·.any Resolved.Expr.isFallibleCall)

end Belay.Sqlite.Model
