import Belay.Sqlite.Model.Resolution.OperandTraced

set_option doc.verso true

/-! The resolution of the expressions of a query without the trace: the projections of
{lit}`resolveOperandTraced`, {lit}`resolveArgumentsTraced` and {lit}`resolveCaseTraced`. -/

namespace Belay.Sqlite.Model

/-- Resolve an expression over the sources in scope (ADR 0012, slice 1): names become column
positions, and each comparison keeps the affinity and collation that evaluation applies. This is
the projection of {name}`resolveOperandTraced`, which states every rule, so the resolved expression
and the name trace come from one decision. -/
def resolveOperand (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (misuse : Bool)
    (expression : Syntax.Expr) : Except ValueIssue Operand :=
  (resolveOperandTraced dqs scope shapes misuse expression).drop

/-- Resolve the arguments of a call in written order, from argument {lit}`index`: the projection of
{name}`resolveArgumentsTraced`. The issue of argument {lit}`k` is at {lit}`[1, k]`. -/
def resolveArguments (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (misuse : Bool) (index : Nat)
    (arguments : List Syntax.Expr) : Except ValueIssue Resolved.Arguments :=
  (resolveArgumentsTraced dqs scope shapes misuse index arguments).drop

/-- Resolve the operands of {lit}`CASE` from operand {lit}`index` as the arguments of {lit}`iif`: the
projection of {name}`resolveCaseTraced`. The issue of operand {lit}`k` is at {lit}`[0, k]`. -/
def resolveCase (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (misuse : Bool) (needsBase : Bool)
    (base : Option (Syntax.Expr × Operand)) (index : Nat) (operands : List Syntax.Expr) :
    Except ValueIssue Resolved.Arguments :=
  (resolveCaseTraced dqs scope shapes misuse needsBase base index operands).drop

end Belay.Sqlite.Model
