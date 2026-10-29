import Belay.Sqlite.Model.ExprCongruence
import Belay.Sqlite.Model.EvalContextLaws

set_option doc.verso true

/-! Appending cells preserves expressions that read only the original row. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every context satisfying {name}`EvalContext.RowFree`, width, row at least that
wide, appended cells and expression whose columns are below the width: appending those cells
preserves its value/fault pair and JSON subtype. Proof sketch: the column bound preserves each read;
row-independent subqueries preserve every subquery observation. -/
theorem Expr.evaluate_append (context : EvalContext) (rowFree : context.RowFree) {width : Nat}
    (row extra : List Value) (wide : width ≤ row.length) (expression : Expr)
    (below : expression.any (Expr.isColumnFrom width) = false) :
    expression.evaluate context (row ++ extra) = expression.evaluate context row ∧
      expression.givesJson context (row ++ extra) = expression.givesJson context row := by
  apply Expr.evaluate_congr context context (row ++ extra) row (Expr.isColumnFrom width) _ expression below
  intro node allowed
  cases node
  case column position =>
    have inside : position < row.length := by
      simp only [Expr.isColumnFrom, ge_iff_le, decide_eq_false_iff_not, Nat.not_le] at allowed
      omega
    simp [Expr.ReadsAgree, List.getD_eq_getElem?_getD, List.getElem?_append_left inside]
  all_goals simp [Expr.ReadsAgree, fun index => rowFree index (row ++ extra) row]

/-- For every context whose subqueries do not depend on the outer row
({name}`EvalContext.RowFree`), width, row with at least that many cells, appended cells and
expression that reads only columns below the width ({name}`Expr.readsBelow`): the expression has
the same value ({name}`Expr.eval`) over the row with the cells appended as over the row. Proof
sketch: {name}`Expr.evaluate_append`. -/
theorem Expr.eval_append (context : EvalContext) (rowFree : context.RowFree) {width : Nat} (row extra : List Value)
    (wide : width ≤ row.length) {expression : Expr} (below : expression.readsBelow width = true) :
    expression.eval context (row ++ extra) = expression.eval context row := by
  unfold Expr.eval
  rw [(Expr.evaluate_append context rowFree row extra wide expression (by simpa [Expr.readsBelow] using below)).1]

end Belay.Sqlite.Model.Resolved
