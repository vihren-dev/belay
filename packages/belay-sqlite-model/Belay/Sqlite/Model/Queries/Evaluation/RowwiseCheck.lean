import Belay.Sqlite.Model.Queries.Evaluation.RowwiseExpr

set_option doc.verso true

/-! A check of the form of a resolved expression that gives {name}`Belay.Sqlite.Model.Resolved.Expr.Rowwise`. The
kernel decides the check for an expression without variables, so a proof about a fixed query can show that its
expressions read only their row and the bound values without a proof for each expression. -/

namespace Belay.Sqlite.Model.Resolved

/-- Whether an expression has only the forms of {name}`Expr.Rowwise`: columns, literals and parameters, combined by
comparisons, {lit}`AND`, {lit}`OR`, {lit}`NOT` and {lit}`IS NULL`. For example, the condition
{lit}`customer_id = ?1 AND expires_at < ?2` passes, and {lit}`EXISTS (SELECT 1)` does not. -/
def Expr.rowwiseCheck : Expr → Bool
  | .column _ | .literal _ | .parameter _ => true
  | .compare _ _ left right _ | .and left right | .or left right => left.rowwiseCheck && right.rowwiseCheck
  | .not operand | .isNull operand _ => operand.rowwiseCheck
  | .arithmetic .. | .cast .. | .coalesce .. | .json .. | .now _ | .counter _ | .date .. | .scalar .. | .exists _
  | .inQuery .. | .subquery _ | .inList .. | .aggregateValue _ => false

/-- For every expression that passes {name}`Expr.rowwiseCheck`, the expression is row-wise
({name}`Expr.Rowwise`). Proof sketch: induction on the expression; each form that the check accepts is a
constructor of {name}`Expr.Rowwise`. -/
theorem Expr.rowwise_of_rowwiseCheck : ∀ {expression : Expr}, expression.rowwiseCheck = true → expression.Rowwise
  | .column _, _ => .column _
  | .literal _, _ => .literal _
  | .parameter _, _ => .parameter _
  | .compare _ _ _ _ _, checked => by
    simp only [Expr.rowwiseCheck, Bool.and_eq_true] at checked
    exact .compare _ _ _ (rowwise_of_rowwiseCheck checked.1) (rowwise_of_rowwiseCheck checked.2)
  | .and _ _, checked => by
    simp only [Expr.rowwiseCheck, Bool.and_eq_true] at checked
    exact .and (rowwise_of_rowwiseCheck checked.1) (rowwise_of_rowwiseCheck checked.2)
  | .or _ _, checked => by
    simp only [Expr.rowwiseCheck, Bool.and_eq_true] at checked
    exact .or (rowwise_of_rowwiseCheck checked.1) (rowwise_of_rowwiseCheck checked.2)
  | .not _, checked => .not (rowwise_of_rowwiseCheck checked)
  | .isNull _ _, checked => .isNull _ (rowwise_of_rowwiseCheck checked)

/-- For every list of expressions that all pass {name}`Expr.rowwiseCheck`, each expression of the list is
row-wise. Proof sketch: {name}`Expr.rowwise_of_rowwiseCheck` for each member. -/
theorem Expr.rowwise_of_all {expressions : List Expr} (checked : expressions.all Expr.rowwiseCheck = true) :
    ∀ expression ∈ expressions, expression.Rowwise :=
  fun _ member => Expr.rowwise_of_rowwiseCheck (List.all_eq_true.mp checked _ member)

/-- For every list of sources whose expressions ({name}`QuerySource.expressions`) all pass
{name}`Expr.rowwiseCheck`, each expression of each source is row-wise. Proof sketch: {name}`Expr.rowwise_of_all`
for each source. -/
theorem QuerySource.rowwise_of_all {sources : List QuerySource}
    (checked : sources.all (fun join => join.expressions.all Expr.rowwiseCheck) = true) :
    ∀ join ∈ sources, ∀ expression ∈ join.expressions, expression.Rowwise :=
  fun join member => Expr.rowwise_of_all (List.all_eq_true.mp checked join member)

end Belay.Sqlite.Model.Resolved
