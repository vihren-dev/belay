import Belay.Sqlite.Model.StatementCalm
import Belay.Sqlite.Model.ExprEvalLaws
import Belay.Sqlite.Model.ExprCongruence
import Belay.Sqlite.Model.IntegerCompareLaws

set_option doc.verso true

/-! Expressions that read only their row and the bound values (ADR 0017, S6). A condition such as
{lit}`customer_id = $c AND expires_at < $now` names columns, literals and parameters, and combines
them with comparisons and logic. Its value does not depend on the subqueries of the context, so a
subquery that runs in a context other than the statement's context still evaluates it in the same way.
The module proves this independence, that such an expression is calm and has no fault, and the
complement law of the guide's purge claim: a row for which the condition {lit}`IS NOT 1` is true is
not selected by the condition. -/

namespace Belay.Sqlite.Model.Resolved

/-- The expressions that read only their row and the bound values: columns, literals, parameters,
comparisons, {lit}`AND`, {lit}`OR`, {lit}`NOT` and {lit}`IS NULL` of such expressions. For example
{lit}`customer_id = $c AND expires_at < $now` is one; an expression with {lit}`EXISTS`, a function call
or a clock read is not. -/
inductive Expr.Rowwise : Expr → Prop where
  /-- A column. -/
  | column (position : Nat) : Rowwise (.column position)
  /-- A literal. -/
  | literal (value : Value) : Rowwise (.literal value)
  /-- A parameter. -/
  | parameter (number : Nat) : Rowwise (.parameter number)
  /-- A comparison of two such expressions. -/
  | compare (operator : Comparison) (affinity : Option Affinity) {left right : Expr} (collation : Collation) :
      Rowwise left → Rowwise right → Rowwise (.compare operator affinity left right collation)
  /-- {lit}`AND` of two such expressions. -/
  | and {left right : Expr} : Rowwise left → Rowwise right → Rowwise (.and left right)
  /-- {lit}`OR` of two such expressions. -/
  | or {left right : Expr} : Rowwise left → Rowwise right → Rowwise (.or left right)
  /-- {lit}`NOT` of such an expression. -/
  | not {operand : Expr} : Rowwise operand → Rowwise (.not operand)
  /-- {lit}`IS NULL` or {lit}`IS NOT NULL` of such an expression. -/
  | isNull {operand : Expr} (negated : Bool) : Rowwise operand → Rowwise (.isNull operand negated)

/-- Every {name}`Expr.Rowwise` expression has no node that reads beyond the row and
parameters. Proof sketch: induction on the syntax certificate, without evaluator reasoning. -/
theorem Expr.Rowwise.localReads {expression : Expr} (rowwise : expression.Rowwise) :
    expression.any Expr.readsBeyondRowAndParameters = false := by
  induction rowwise <;> simp_all [Expr.any, Expr.readsBeyondRowAndParameters]

/-- For every row-wise expression, row and two contexts with equal parameter lists, the
value/fault pair is equal. Proof sketch: {name}`Expr.Rowwise.localReads` supplies the read
boundary to {name}`Expr.evaluate_rowAndParameters`; project the pair equality. -/
theorem Expr.Rowwise.evaluate_congr {expression : Expr} (rowwise : expression.Rowwise) (first second : EvalContext)
    (row : List Value) (same : first.parameters = second.parameters) :
    expression.evaluate first row = expression.evaluate second row :=
  (expression.evaluate_rowAndParameters rowwise.localReads first second row same).1

/-- For every row-wise expression, context and row, the evaluation has no fault. Proof sketch: induction over
the expression; no form of it can fail, and the join and the softening of no faults is no fault. -/
theorem Expr.Rowwise.fault_none {expression : Expr} (rowwise : expression.Rowwise) (context : EvalContext)
    (row : List Value) : (expression.evaluate context row).2 = .none := by
  induction rowwise with
  | column | literal | parameter => simp [Expr.evaluate]
  | compare _ _ _ _ _ left right => simp [Expr.evaluate, left, right, Fault.join]
  | and _ _ left right => simp [Expr.evaluate, left, right, Fault.join, Fault.soften]
  | or _ _ left right => simp [Expr.evaluate, left, right, Fault.join, Fault.soften]
  | not _ ih => simp [Expr.evaluate, ih]
  | isNull _ _ ih => simp [Expr.evaluate, ih]

/-- Every row-wise expression is calm ({name}`Expr.Calm`): it has no fallible call, reads no clock and calls
no counter function. Proof sketch: induction over the expression; the parts of each form are calm. -/
theorem Expr.Rowwise.calm {expression : Expr} (rowwise : expression.Rowwise) : expression.Calm := by
  induction rowwise with
  | column | literal | parameter =>
    simp [Expr.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere]
  | compare _ _ _ _ _ left right | and _ _ left right | or _ _ left right =>
    simp_all [Expr.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere]
  | not _ ih | isNull _ _ ih =>
    simp_all [Expr.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere]

/-- For every two values, {lit}`a AND b` is NULL, 0 or 1. Proof sketch: the definition of the value has three
results. -/
theorem Value.and_cases (a b : Value) :
    Value.and a b = .null ∨ Value.and a b = .integer 0 ∨ Value.and a b = .integer 1 := by
  unfold Value.and
  by_cases h : (falsy a || falsy b) = true
  · simp [h, truth]
  · by_cases n : (a.isNull || b.isNull) = true <;> simp [h, n, truth]

/-- For every value that is NULL, 0 or 1: if {lit}`value IS NOT 1` is true, the value is not true. In plain
words: a row that the condition {lit}`IS NOT 1` accepts is a row that the condition itself does not select, even
when the condition is NULL. Proof sketch: the three values, with the comparison of the integers 0 and 1. -/
theorem truthy_isNot_one_of_cases (value : Value)
    (cases : value = .null ∨ value = .integer 0 ∨ value = .integer 1) :
    truthy (Comparison.apply .isNot value (.integer 1)) = true → truthy value = false := by
  rcases cases with rfl | rfl | rfl <;>
    simp [Comparison.apply, truth, truthy, Value.isNull, Collation.compare_integer, Comparison.holds]

/-- For every two conditions, context and row: if {lit}`(left AND right) IS NOT 1` is true for the row, then
{lit}`left AND right` is not true for it. In plain words: a row that the NULL-aware condition accepts is a row that a
{lit}`DELETE` with the condition {lit}`left AND right` does not select, whatever the values of the parameters are
(NULL and text included). Proof sketch: {name}`Value.and_cases` and {name}`truthy_isNot_one_of_cases`. -/
theorem Expr.truthy_isNot_one_and (left right : Expr) (context : EvalContext) (row : List Value) :
    truthy ((Expr.compare .isNot none (.and left right) (.literal (.integer 1))).eval context row) = true →
      truthy ((Expr.and left right).eval context row) = false := by
  simp only [Expr.eval, Expr.evaluate, comparisonOperands]
  exact truthy_isNot_one_of_cases _ (Value.and_cases _ _)

end Belay.Sqlite.Model.Resolved
