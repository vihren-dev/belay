import Belay.Sqlite.Model.Shared.Catalog.ExprAny

set_option doc.verso true

namespace Belay.Sqlite.Model

open Resolved

/-- For every width, larger width and expression: if the expression reads no column at or after the
width ({name}`Expr.isColumnFrom`, {name}`Expr.any`), it reads none at or after the larger width.
Proof sketch: induction over the mutual expression and argument types; a column below the width is
below the larger width, and every other node combines its parts. -/
theorem Expr.any_isColumnFrom_mono {width other : Nat} (le : width ≤ other) (expression : Expr)
    (below : expression.any (Expr.isColumnFrom width) = false) :
    expression.any (Expr.isColumnFrom other) = false := by
  induction expression using Expr.rec
    (motive_2 := fun arguments => arguments.any (Expr.isColumnFrom width) = false →
      arguments.any (Expr.isColumnFrom other) = false)
  all_goals simp_all [Expr.any, Arguments.any, Expr.isColumnFrom]
  all_goals omega

/-- For every expression that reads only columns below a width and every larger width, the
expression reads only columns below the larger width ({name}`Expr.readsBelow`). Proof sketch:
{name}`Expr.any_isColumnFrom_mono`. -/
theorem Expr.readsBelow_mono {width other : Nat} (le : width ≤ other) {expression : Expr}
    (below : expression.readsBelow width = true) : expression.readsBelow other = true := by
  simp only [Expr.readsBelow, Bool.not_eq_true'] at below ⊢
  exact Expr.any_isColumnFrom_mono le expression below

end Belay.Sqlite.Model
