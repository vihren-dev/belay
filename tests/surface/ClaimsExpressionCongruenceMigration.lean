import Belay.Sqlite.Model.ExprAppendLaws
import Belay.Sqlite.Model.ExprContextLaws
import Belay.Sqlite.Model.RowwiseExpr

set_option doc.verso true

/-! Temporary recovery of the four formulas from main 3e2212ed. Retire after final Nix
acceptance of the last planned contract change, as the expression-congruence task requires. -/

open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- The original append formula, including its width, RowFree and subtype obligations. -/
example (context : EvalContext) (rowFree : context.RowFree) {width : Nat} (row extra : List Value)
    (wide : width ≤ row.length) (expression : Expr) (below : expression.any (Expr.isColumnFrom width) = false) :
    expression.evaluate context (row ++ extra) = expression.evaluate context row ∧
      expression.givesJson context (row ++ extra) = expression.givesJson context row :=
  expression.evaluate_append context rowFree row extra wide below

/-- The original replacement formula follows with its former no-fallible-call premise. -/
example (context : EvalContext) (row : List Value) (other : Nat → List Value → SubqueryRun)
    (agree : ∀ index, context.subqueries index row = other index row) (expression : Expr)
    (_plain : expression.any Expr.isFallibleCall = false) :
    expression.evaluate { context with subqueries := other } row = expression.evaluate context row :=
  (expression.evaluate_withSubqueries context row other agree).1

/-- The original certainty formula keeps both original premises. -/
example (context : EvalContext) (row : List Value) (expression : Expr)
    (noScalar : expression.any (· matches .subquery _) = false)
    (_plain : expression.any Expr.isFallibleCall = false) :
    expression.evaluate { context with subqueries := fun index outer =>
      (context.subqueries index outer).certainFirst } row = expression.evaluate context row :=
  (expression.evaluate_certainFirst context row noScalar).1

/-- The original Rowwise formula needs only equal parameters at the same row. -/
example {expression : Expr} (rowwise : expression.Rowwise) (first second : EvalContext)
    (row : List Value) (same : first.parameters = second.parameters) :
    expression.evaluate first row = expression.evaluate second row :=
  rowwise.evaluate_congr first second row same
