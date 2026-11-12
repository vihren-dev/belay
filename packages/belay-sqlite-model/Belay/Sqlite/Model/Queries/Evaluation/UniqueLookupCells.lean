import Belay.Sqlite.Model.Values.Scalar.LiteralData
import Belay.Sqlite.Model.Queries.Evaluation.IntegerCompareLaws
import Belay.Sqlite.Model.Queries.Evaluation.ExprFault

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every collation and value, the collation key of the value has the same storage class
({name}`Value.rank`) as the value. Proof sketch: case analysis on the collation and the value. -/
theorem Collation.key_rank (collation : Collation) (value : Value) : (collation.key value).rank = value.rank := by
  cases collation <;> cases value <;> simp [Collation.key, Value.rank]

/-- For every collation and two values of different storage classes ({name}`Value.rank`), the comparison of the
values under the collation is not {lean}`Ordering.eq`. Proof sketch: the comparison starts with the ranks of the
keys ({name}`Collation.key_rank`), which differ. -/
theorem Collation.compare_ne_of_rank_ne (collation : Collation) {first second : Value}
    (different : first.rank ≠ second.rank) : collation.compare first second ≠ .eq := by
  have ranks : Ord.compare (collation.key first).rank (collation.key second).rank ≠ .eq := by
    rw [Collation.key_rank, Collation.key_rank]
    exact fun equal => different (Nat.compare_eq_eq.1 equal)
  unfold Collation.compare Value.compare compareLex compareOn
  generalize Ord.compare (collation.key first).rank (collation.key second).rank = order at ranks ⊢
  cases order <;> simp_all [Ordering.then]

namespace Resolved

/-- The value that a stored cell is compared with in {lit}`c = v`, for a comparison with the affinity of the column
({name}`comparisonOperands`): with INTEGER, REAL or NUMERIC affinity the value after
{name}`numericOperand`; with TEXT affinity the value after {name}`Value.store` of TEXT; with BLOB affinity or none the
value itself. -/
def comparisonProbe : Option Affinity → Value → Value
  | some .integer, value | some .real, value | some .numeric, value => numericOperand value
  | some .text, value => Value.store .text value
  | some .blob, value | none, value => value

end Resolved
end Belay.Sqlite.Model
