import Belay.Sqlite.Model.Schema.Writes.JsonReady
import Belay.Sqlite.Model.Queries.Evaluation.RowwiseExpr

set_option doc.verso true

/-! Laws of the readiness checks of the writes ({lit}`deleteJsonReady`). A kind rule of a write continues only
when its check is true, so a proof that the step of a write continues needs the value of the check. -/

namespace Belay.Sqlite.Model

/-- For every optional filter whose expression is row-wise ({name}`Resolved.Expr.Rowwise`), context, table and list
of {lit}`RETURNING` columns: the check {name}`deleteJsonReady` of a DELETE is true exactly when no {lit}`RETURNING`
expression has a fallible call. In plain words, a row-wise filter or no filter never makes a DELETE unready,
whatever the rows of the table and the parameters, the clock, the counters and the subqueries of the context are.
For a DELETE without {lit}`RETURNING` the check is true. Proof sketch: the test of the filter is
{name}`Resolved.anyMayFail_of_rowwise`. -/
theorem deleteJsonReady_of_rowwise {filter : Option Resolved.Expr}
    (rowwise : ∀ expression ∈ filter.toList, expression.Rowwise) (context : Resolved.EvalContext) (table : Table)
    (returning : List (Resolved.Expr × String)) :
    deleteJsonReady context table filter returning =
      !(returningExpressions returning).any (·.any Resolved.Expr.isFallibleCall) := by
  simp [deleteJsonReady, Resolved.anyMayFail_of_rowwise rowwise]

end Belay.Sqlite.Model
