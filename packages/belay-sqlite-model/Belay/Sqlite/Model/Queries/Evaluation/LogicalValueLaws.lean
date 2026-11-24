import Belay.Sqlite.Model.Queries.Evaluation.ExprEvalLaws
import Belay.Sqlite.Model.Queries.Evaluation.IntegerCompareLaws

set_option doc.verso true

/-! Expressions whose value is NULL, 0 or 1 (ADR 0017, S6). A comparison, {lit}`AND`, {lit}`OR`, {lit}`NOT`,
{lit}`IS NULL`, {lit}`EXISTS` and {lit}`IN` give such a value. For such a value, {lit}`v IS NOT 1` is true exactly when
{lit}`v` is not true, also when {lit}`v` is NULL. So a claim with the condition {lit}`f IS NOT 1` keeps exactly the
rows that a {lit}`DELETE` with the filter {lit}`f` does not select. A column or a literal can have another value: for
the value 2, both {lit}`2` and {lit}`2 IS NOT 1` are true. -/

namespace Belay.Sqlite.Model

/-- A value that is NULL, or 1 or 0 ({name}`Model.truth`). -/
def Value.IsLogical (value : Value) : Prop :=
  value = .null ∨ ∃ holds, value = Model.truth holds

/-- For every operator, two values and collation, the comparison is NULL, 0 or 1. Proof sketch: each operator gives
NULL or {name}`truth` of a Boolean. -/
theorem Comparison.apply_isLogical (operator : Comparison) (left right : Value) (collation : Collation) :
    Value.IsLogical (operator.apply left right collation) := by
  unfold Value.IsLogical Comparison.apply
  cases operator <;> dsimp only <;> repeat (first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩ | split)

/-- For every value that is NULL, 0 or 1 and every collation, {lit}`value IS NOT 1` is true exactly when the value is
not true. In plain words: NULL and 0 are not 1, and 1 is 1. Proof sketch: the three values, with the comparison of
two integers ({name}`Collation.compare_integer`). -/
theorem Value.truthy_isNot_one {value : Value} (logical : value.IsLogical) (collation : Collation) :
    Resolved.truthy (Comparison.apply .isNot value (.integer 1) collation) = !Resolved.truthy value := by
  rcases logical with rfl | ⟨holds, rfl⟩
  · rfl
  · cases holds <;>
      simp [Comparison.apply, Model.truth, Resolved.truthy, Collation.compare_integer, Value.isNull, Comparison.holds]

end Belay.Sqlite.Model

namespace Belay.Sqlite.Model.Resolved

/-- Whether the outer node of an expression is one of the forms that always give NULL, 0 or 1: a comparison,
{lit}`AND`, {lit}`OR`, {lit}`NOT`, {lit}`IS NULL`, {lit}`EXISTS` or {lit}`IN`. The check reads only the outer node.
For every other form it is false, and then it gives no conclusion about the value: the literal {lit}`1` has the value
1, and the column with the value 2 has the value 2. -/
def Expr.isLogical : Expr → Bool
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .exists _ | .inQuery .. | .inList .. => true
  | .column _ | .literal _ | .arithmetic .. | .cast .. | .coalesce .. | .json .. | .now _ | .parameter _
  | .counter _ | .date .. | .scalar .. | .subquery _ | .aggregateValue _ => false

/-- For every affinity, collation, negation, value and candidates, the value of {lit}`IN` ({name}`inValue`) is NULL,
0 or 1. Proof sketch: each branch of the definition gives NULL or {name}`truth` of a Boolean. -/
theorem inValue_isLogical (affinity : Option Affinity) (collation : Collation) (negated : Bool) (value : Value)
    (candidates : List Value) : Value.IsLogical (inValue affinity collation negated value candidates) := by
  unfold Value.IsLogical inValue
  repeat (first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩ | split)

/-- For every expression whose top node gives a logical value ({name}`Expr.isLogical`), every context and row, the
value of the expression is NULL, 0 or 1. Proof sketch: a case for each form; {lit}`AND`, {lit}`OR` and {lit}`NOT` give
NULL or {name}`truth` by their definitions, and the comparison and {lit}`IN` by
{name}`Comparison.apply_isLogical` and {name}`inValue_isLogical`. -/
theorem Expr.eval_isLogical {expression : Expr} (logical : expression.isLogical = true) (context : EvalContext)
    (row : List Value) : Value.IsLogical (expression.eval context row) := by
  cases expression <;> simp only [Expr.isLogical, Bool.false_eq_true] at logical <;>
    simp only [Expr.eval, Expr.evaluate]
  case compare => exact Comparison.apply_isLogical _ _ _ _
  case inQuery => exact inValue_isLogical _ _ _ _ _
  case inList => exact inValue_isLogical _ _ _ _ _
  all_goals
    unfold Value.IsLogical
    try unfold Value.and
    try unfold Value.or
    try unfold Value.not
    repeat (first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩ | split)

/-- For every expression whose top node gives a logical value ({name}`Expr.isLogical`), collation, context and row,
the condition {lit}`expression IS NOT 1`, without affinity, is true for the row exactly when the expression is not
true for it. In plain words: the condition keeps exactly the rows that a {lit}`DELETE` with the expression as its
filter does not select, also when the expression is NULL. Proof sketch: {name}`Expr.eval_isLogical` and
{name}`Value.truthy_isNot_one`. -/
theorem Expr.truthy_isNot_one {expression : Expr} (logical : expression.isLogical = true) (collation : Collation)
    (context : EvalContext) (row : List Value) :
    truthy ((Expr.compare .isNot none expression (.literal (.integer 1)) collation).eval context row) =
      !truthy (expression.eval context row) := by
  have result := Value.truthy_isNot_one (expression.eval_isLogical logical context row) collation
  simpa only [Expr.eval, Expr.evaluate, comparisonOperands] using result

end Belay.Sqlite.Model.Resolved
