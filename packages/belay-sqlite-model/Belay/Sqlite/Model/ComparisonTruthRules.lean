import Belay.Sqlite.Model.ExprEvalLaws

set_option doc.verso true

/-! The truth rules of a comparison in a {lit}`WHERE` condition (ADR 0027 D1, expression phase):
the affinity of a comparison ({name}`Belay.Sqlite.Model.Resolved.comparisonOperands`) converts no
value to NULL and no NULL to a value, so {lit}`x IS NOT NULL` is true exactly when {lit}`x` is not
NULL under every affinity and collation, and an ordinary comparison that is true has two operands
that are not NULL and whose converted values satisfy the operator. These are the facts that a
filter gives to the rows that it keeps. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every value, the numeric conversion of a comparison operand ({name}`numericOperand`) is
NULL exactly when the value is NULL. Proof sketch: cases on the value; the conversion of a text
gives a number or the text. -/
theorem numericOperand_isNull (value : Value) : (numericOperand value).isNull = value.isNull := by
  cases value with
  | text bytes =>
    simp only [numericOperand, numericText, textNumber]
    split
    · rfl
    · split
      · rfl
      · simp only [Option.getD_some, integerAffinity]
        cases wholeReal _ <;> rfl
  | _ => rfl

/-- For every affinity and two values, each operand that the affinity of a comparison gives
({name}`comparisonOperands`) is NULL exactly when its value is NULL. Proof sketch: cases on the
affinity; the numeric conversion keeps NULL and non-NULL ({name}`numericOperand_isNull`), and the
text conversion of a stored value too. -/
theorem comparisonOperands_isNull (affinity : Option Affinity) (left right : Value) :
    (comparisonOperands affinity left right).1.isNull = left.isNull ∧
      (comparisonOperands affinity left right).2.isNull = right.isNull := by
  rcases affinity with _ | affinity
  · simp [comparisonOperands]
  · cases affinity <;> simp only [comparisonOperands, numericOperand_isNull, and_self]
    split <;> cases left <;> cases right <;> simp_all [Value.store, Value.isNull]

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
