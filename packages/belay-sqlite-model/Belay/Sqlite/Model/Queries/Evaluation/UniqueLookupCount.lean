import Belay.Sqlite.Model.Queries.Evaluation.UniqueLookupCompare
import Belay.Sqlite.Model.Queries.Evaluation.CountMatchingLaws
import Belay.Sqlite.Model.Queries.Evaluation.SelectCalmRule
import Belay.Sqlite.Model.Queries.Evaluation.ExprEvalLaws
import Belay.Sqlite.Model.Queries.Evaluation.EvalContextLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

namespace Resolved

/-- For every parameters and number of rows: the condition {lit}`n <= 1`, with the subquery value {lit}`n`
({name}`Resolved.SubqueryRun.count`) in the context of the parameters, with no affinity, under the binary collation,
against the integer literal 1, is true ({name}`truthy`) exactly when the number
is at most one. Proof sketch: the comparison of two integers under any collation is the order of the integers
({name}`Collation.compare_integer`). -/
theorem truthy_count_le_one (parameters : List Value) (n : Nat) :
    truthy ((Expr.compare .le none (.subquery 0) (.literal (.integer 1)) .binary).eval
      ((EvalContext.bound parameters).withRuns [SubqueryRun.count n]) []) = decide (n ≤ 1) := by
  simp [Expr.eval_compare, Expr.eval_subquery, Expr.eval_literal, EvalContext.withRuns_subqueries, comparisonOperands,
    SubqueryRun.count, Value.isNull, Comparison.holds, Collation.compare_integer, truth, truthy, Comparison.apply]
  rcases Int.lt_trichotomy (n : Int) 1 with less | equal | greater
  · simp [Int.compare_eq_lt.2 less, show n ≤ 1 by omega]
  · simp [equal, show n ≤ 1 by omega]
  · simp [Int.compare_eq_gt.2 greater, show ¬ n ≤ 1 by omega]

end Resolved

end Belay.Sqlite.Model
