import Belay.Sqlite.Model.Queries.Select.SimpleStatementResolution
import Belay.Sqlite.Model.Queries.Evaluation.StatementCalm
import Belay.Sqlite.Model.Queries.Select.ExprAnyLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whether an expression is a function call, {lit}`f(*)` or {lit}`f(x, ...)`. The result column of an aggregate
function is no scalar, so the operand-based convenience laws exclude calls; the column-resolution
primitive also covers scalar calls. -/
def Syntax.Expr.isCall : Syntax.Expr → Bool
  | .callStar _ | .call .. => true
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .identifier .. | .qualified ..
  | .negate _ | .positive _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic .. | .cast ..
  | .collate .. | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf .. | .concatenate ..
  | .raise .. => false

/-- A result column that is an expression other than a function call, without an alias, resolves in any scope to
the scalar column of the resolved expression, named by the defined name of the expression or else by its text,
with the affinity of the expression, when the expression resolves as an operand that is no condition. Proof
sketch: unfold {name}`resolveResultColumn`; every other form of expression takes the last branch. -/
theorem resolveColumns_scalar (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (value : Syntax.Expr) (text : String)
    (expression : Resolved.Expr) (affinity : Option Affinity) (notCall : value.isCall = false)
    (operand : resolveOperand dqs scope shapes false value = .ok (expression, affinity)) :
    resolveAll (resolveResultColumn dqs scope shapes) [.expression value none text] =
      .ok [[(.scalar expression, (definedName scope value).getD text, affinity)]] := by
  cases value <;> simp_all [Syntax.Expr.isCall, resolveAll, resolveAllFrom, resolveResultColumn_expression, Bind.bind, Except.bind,
    Pure.pure, Except.pure, Except.mapError]

end Belay.Sqlite.Model
