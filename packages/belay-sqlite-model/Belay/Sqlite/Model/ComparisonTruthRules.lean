import Belay.Sqlite.Model.ExprEvalLaws
import Belay.Sqlite.Model.InValueEqualsLaws

set_option doc.verso true

/-! The truth rules of a comparison in a {lit}`WHERE` condition (ADR 0027 D1, expression phase):
the affinity of a comparison ({name}`Belay.Sqlite.Model.Resolved.comparisonOperands`) converts no
value to NULL and no NULL to a value, so {lit}`x IS NOT NULL` is true exactly when {lit}`x` is not
NULL under every affinity and collation, and an ordinary comparison that is true has two operands
that are not NULL and whose converted values satisfy the operator. These are the facts that a
filter gives to the rows that it keeps. -/

namespace Belay.Sqlite.Model.Resolved

/-- {lit}`x IS NOT NULL`: for every affinity, collation and value, the comparison {lit}`IS NOT`
of the value with NULL is true exactly when the value is not NULL. Proof sketch: the affinity
keeps both operands NULL or not ({name}`comparisonOperands_isNull`), and {lit}`IS NOT` with a
NULL operand tests the other. -/
theorem truthy_isNot_null (affinity : Option Affinity) (collation : Collation) (value : Value) :
    truthy (Comparison.isNot.apply (comparisonOperands affinity value .null).1
      (comparisonOperands affinity value .null).2 collation) = !value.isNull := by
  obtain ⟨first, second⟩ := comparisonOperands_isNull affinity value .null
  have null : (comparisonOperands affinity value .null).2.isNull = true := by rw [second]; rfl
  simp only [Comparison.apply, null, Bool.or_true, ite_true, first]
  cases value.isNull <;> rfl

/-- An ordinary comparison that is true: for every operator other than {lit}`IS` and
{lit}`IS NOT`, affinity, collation and two values, when the comparison of the converted values
({name}`comparisonOperands`) is true, then neither value is NULL and the converted values satisfy
the operator under the collation ({name}`Comparison.holds`). Proof sketch:
{name}`truthy_apply_ordinary` with {name}`comparisonOperands_isNull`. -/
theorem ordinary_of_truthy {operator : Comparison} (notIs : operator ≠ .is) (notIsNot : operator ≠ .isNot)
    {affinity : Option Affinity} {collation : Collation} {left right : Value}
    (holds : truthy (operator.apply (comparisonOperands affinity left right).1
      (comparisonOperands affinity left right).2 collation) = true) :
    left.isNull = false ∧ right.isNull = false ∧
      operator.holds (collation.compare (comparisonOperands affinity left right).1
        (comparisonOperands affinity left right).2) = true := by
  rw [truthy_apply_ordinary operator notIs notIsNot] at holds
  obtain ⟨first, second⟩ := comparisonOperands_isNull affinity left right
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at holds
  exact ⟨first ▸ holds.1.1, second ▸ holds.1.2, holds.2⟩

end Belay.Sqlite.Model.Resolved
