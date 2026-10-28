import Belay.Sqlite.Model.ExprCongruence
import Belay.Sqlite.Model.ExprAnyLaws
import Belay.Sqlite.Model.EvalContextLaws

set_option doc.verso true

/-! Replacing unobserved subquery data preserves expression results and JSON subtype. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every context, row, replacement subquery function and expression: if each
indexed subquery run agrees at that row, replacement preserves the expression's value/fault
pair and JSON subtype. Fallible calls are allowed. Proof sketch: every primitive observation
agrees, so apply {name}`Expr.evaluate_congr`. -/
theorem Expr.evaluate_withSubqueries (context : EvalContext) (row : List Value)
    (other : Nat → List Value → SubqueryRun) (agree : ∀ index, context.subqueries index row = other index row)
    (expression : Expr) :
    expression.evaluate { context with subqueries := other } row = expression.evaluate context row ∧
      expression.givesJson { context with subqueries := other } row = expression.givesJson context row := by
  apply Expr.evaluate_congr _ _ row row (fun _ => false) _ expression (Expr.any_false expression)
  intro node _
  cases node <;> simp [Expr.ReadsAgree, ← agree]

/-- For every context, row and expression with no scalar subquery at any depth:
marking every subquery's first row certain preserves the value/fault pair and JSON subtype.
Fallible calls are allowed. Existence and membership do not inspect that certainty field. Proof sketch:
each admitted node observes the same data, then apply the shared evaluator theorem. -/
theorem Expr.evaluate_certainFirst (context : EvalContext) (row : List Value) (expression : Expr)
    (noScalar : expression.any (· matches .subquery _) = false) :
    expression.evaluate { context with subqueries := fun index outer => (context.subqueries index outer).certainFirst } row =
      expression.evaluate context row ∧
    expression.givesJson { context with subqueries := fun index outer => (context.subqueries index outer).certainFirst } row =
      expression.givesJson context row := by
  apply Expr.evaluate_congr _ _ row row (· matches .subquery _) _ expression noScalar
  intro node allowed
  cases node <;> simp_all [Expr.ReadsAgree, SubqueryRun.certainFirst]
  all_goals rfl

end Belay.Sqlite.Model.Resolved
