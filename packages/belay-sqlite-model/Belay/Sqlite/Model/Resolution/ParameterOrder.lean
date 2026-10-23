import Belay.Sqlite.Model.Resolution.QueryExprs

set_option doc.verso true

/-! Where SQLite reports a parameter that it prohibits (ADR 0019, D1). SQLite gives
{lit}`parameters prohibited in ...` while it walks the names of a {lit}`CHECK` constraint, a
generated column, an index expression or the filter of a partial index, in the order of the
text. A name that does not resolve or a subquery before the first parameter comes first; the
other errors of the expression come after it, such as {lit}`.`, an unknown function, a
non-deterministic function, a misused aggregate or an unknown collation (checked natively,
3.51.0). -/

namespace Belay.Sqlite.Model.Syntax

/-- Whether a name fails to resolve over the scope, as {name}`resolveOperand` reports it with
a prepare error. A name that resolves, a double-quoted text and the restriction of a rowid
name do not fail. -/
def nameFails (dqs : Bool) (scope : Scope) (name : Expr) : Bool :=
  match resolveOperand dqs scope {} true name with
  | .error (.prepare _) => true
  | .error (.restriction ..) | .ok _ => false

mutual
/-- What comes first in an expression in the order of the text: {lit}`some true` for a
parameter, {lit}`some false` for a name that fails ({name}`nameFails`) or a subquery, and none
when the expression has neither. -/
def Expr.parameterFirst (dqs : Bool) (scope : Scope) : Expr → Option Bool
  | .parameter _ => some true
  | name@(.identifier ..) | name@(.qualified ..) => if nameFails dqs scope name then some false else none
  | .exists _ | .subquery _ | .inQuery .. => some false
  | .compare _ left right | .and left right | .or left right | .arithmetic _ left right | .concatenate left right =>
    (left.parameterFirst dqs scope).orElse fun _ => right.parameterFirst dqs scope
  | .not operand | .isNull operand _ | .negate operand | .positive operand | .cast operand _
  | .collate operand _ => operand.parameterFirst dqs scope
  | .call _ arguments | .caseOf arguments _ => Expr.listParameterFirst dqs scope arguments
  | .inList operand values _ =>
    (operand.parameterFirst dqs scope).orElse fun _ => Expr.listParameterFirst dqs scope values
  | .between operand low high _ =>
    ((operand.parameterFirst dqs scope).orElse fun _ => low.parameterFirst dqs scope).orElse fun _ =>
      high.parameterFirst dqs scope
  | .raise _ (some message) => message.parameterFirst dqs scope
  | .raise _ none | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .callStar _ => none

/-- What comes first in the expressions of a list, in order ({name}`Expr.parameterFirst`). -/
def Expr.listParameterFirst (dqs : Bool) (scope : Scope) : List Expr → Option Bool
  | [] => none
  | expression :: rest => (expression.parameterFirst dqs scope).orElse fun _ => Expr.listParameterFirst dqs scope rest
end

end Belay.Sqlite.Model.Syntax

namespace Belay.Sqlite.Model

/-- SQLite's error of a prohibited parameter, when a parameter of the expression comes before
every name that fails and every subquery ({name}`Syntax.Expr.parameterFirst`); else nothing,
and the resolution of the expression reports its own errors. -/
def prohibitParameter (dqs : Bool) (scope : Scope) (error : ExprError) (expression : Syntax.Expr) :
    Except ValueIssue Unit :=
  if expression.parameterFirst dqs scope == some true then throw (.prepare error) else pure ()

end Belay.Sqlite.Model
