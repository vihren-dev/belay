import Belay.Sqlite.Model.Queries.Evaluation.InSubqueryFilterLaw

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- If the second operand {lit}`probe` has the probe value in every joined row, the correlated condition
{lit}`e = probe` of the subquery keeps a joined row exactly when the {lit}`IN` subquery without a condition would keep it
and {lit}`e` equals the probe value. In symbols: {name}`CorrelatedEquality` for no condition of the {lit}`IN` subquery and
the condition {lit}`Expr.compare .eq` of the result expression and the probe expression. Proof sketch: the evaluation of
the comparison is {name}`equalsValue` of the operands. -/
theorem correlatedEquality_of_compare (inner : EvalContext) (affinity : Option Affinity) (collation : Collation)
    (projection probeInner : Expr) (value : Value) (rows : List (List Value))
    (sameProbe : ∀ row ∈ rows, probeInner.eval inner row = value) :
    CorrelatedEquality inner affinity collation none (some (.compare .eq affinity projection probeInner collation))
      projection value rows := by
  intro row member
  have probe := sameProbe row member
  subst probe
  rfl

end Belay.Sqlite.Model.Resolved
