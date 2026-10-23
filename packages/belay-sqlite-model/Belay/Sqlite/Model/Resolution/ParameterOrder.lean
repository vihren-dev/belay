import Belay.Sqlite.Model.Resolution.QueryExprs
import Belay.Sqlite.Model.Resolution.SyntaxParameters

set_option doc.verso true

/-! Where SQLite reports a parameter that it prohibits (ADR 0019, D1). SQLite gives
{lit}`parameters prohibited in ...` while it walks the names of a {lit}`CHECK` constraint, a
generated column, an index expression or the filter of a partial index. Which error of the
walk SQLite reports depends on the order of the walk and on the errors before the parameter:
an error replaces an earlier message, some forms stop the walk, and a function call ends the
stop of its arguments (checked natively, 3.51.0). The model gives the parameter's error only
for an expression where the parameter is the only error that the walk can find
({lit}`Syntax.Expr.parameterOnly`), and the restriction
{lit}`parameterErrorOrder` for every other expression with a parameter. -/

namespace Belay.Sqlite.Model

/-- Whether a name resolves over the scope: {name}`resolveOperand` gives no prepare error. A
double-quoted text and the restriction of a rowid name resolve. -/
def nameResolves (dqs : Bool) (scope : Scope) (name : Syntax.Expr) : Bool :=
  match resolveOperand dqs scope {} true name with
  | .error (.prepare _) => false
  | .error (.restriction ..) | .ok _ => true

mutual
/-- Whether an expression has no form that can give another error than a parameter in
SQLite's walk of names, or that SQLite removes before the walk: each name resolves, and the
expression has no function call, time keyword, subquery, {lit}`RAISE`, qualified name,
unknown collation, {lit}`IN ()` or {lit}`AND` with a number. -/
def Syntax.Expr.parameterOnly (dqs : Bool) (scope : Scope) : Syntax.Expr → Bool
  | name@(.identifier ..) => nameResolves dqs scope name
  | .parameter _ | .null | .numeric _ | .string _ | .blob _ => true
  | .qualified .. | .call .. | .callStar _ | .currentTime _ | .exists _ | .subquery _ | .inQuery ..
  | .raise .. => false
  | .and left right =>
    !(left matches .numeric _) && !(right matches .numeric _) && left.parameterOnly dqs scope &&
      right.parameterOnly dqs scope
  | .compare _ left right | .or left right | .arithmetic _ left right | .concatenate left right =>
    left.parameterOnly dqs scope && right.parameterOnly dqs scope
  | .collate operand name => (Collation.named? name).isSome && operand.parameterOnly dqs scope
  | .not operand | .isNull operand _ | .negate operand | .positive operand | .cast operand _ =>
    operand.parameterOnly dqs scope
  | .caseOf arguments _ => Syntax.Expr.listParameterOnly dqs scope arguments
  | .inList operand values _ =>
    !values.isEmpty && operand.parameterOnly dqs scope && Syntax.Expr.listParameterOnly dqs scope values
  | .between operand low high _ =>
    operand.parameterOnly dqs scope && low.parameterOnly dqs scope && high.parameterOnly dqs scope

/-- Whether each expression of the list is {name}`Syntax.Expr.parameterOnly`. -/
def Syntax.Expr.listParameterOnly (dqs : Bool) (scope : Scope) : List Syntax.Expr → Bool
  | [] => true
  | expression :: rest => expression.parameterOnly dqs scope && Syntax.Expr.listParameterOnly dqs scope rest
end

/-- SQLite's error where a parameter is prohibited: nothing for an expression without a
parameter, whose resolution reports its own errors; the error of the parameter when it is the
only error that SQLite's walk can find ({name}`Syntax.Expr.parameterOnly`); else the
restriction {name}`RestrictionKind.parameterErrorOrder`. -/
def prohibitParameter (dqs : Bool) (scope : Scope) (error : ExprError) (expression : Syntax.Expr) :
    Except ValueIssue Unit :=
  if !expression.hasParameter then pure ()
  else if expression.parameterOnly dqs scope then throw (.prepare error)
  else throw (.restriction [] .parameterErrorOrder)

end Belay.Sqlite.Model
