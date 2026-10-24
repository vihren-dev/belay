import Belay.Sqlite.Model.SimpleStatementResolution
import Belay.Sqlite.Model.StatementCalm
import Belay.Sqlite.Model.ExprAnyLaws

set_option doc.verso true

/-! The resolution of {lit}`SELECT e` and {lit}`SELECT e WHERE c` without {lit}`FROM` (ADR 0017, S4), the query
form of a value that needs no table: when {lit}`e` is no function call, the statement resolves to the simple query
without source, the expression that {lit}`e` resolves to in the empty scope, and the condition that {lit}`c`
resolves to. -/

namespace Belay.Sqlite.Model

/-- Whether an expression is a function call, {lit}`f(*)` or {lit}`f(x, ...)`. The result column of an aggregate
function is no scalar, so the laws of {lit}`SELECT e` exclude calls. -/
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
  cases value <;> simp_all [Syntax.Expr.isCall, resolveAll, resolveAllFrom, resolveResultColumn, Bind.bind, Except.bind,
    Pure.pure, Except.pure, Except.mapError]

/-- For every statement {lit}`SELECT e` (or {lit}`SELECT e WHERE c`) without {lit}`FROM`, where {lit}`e` is no
function call and has no aggregate call inside, and resolves in the empty scope to an expression without a fallible call, and the condition resolves in
the empty scope to a condition ({name}`FilterResolves`), resolution gives the simple query without source, with that
condition and the one scalar column of the expression, and leaves the state as it is. Proof sketch:
{name}`resolveStatement_select_simple` with the empty source of {name}`resolveSources_none`, the column of
{name}`resolveColumns_scalar`, and no aggregate value below a fallible call ({name}`Resolved.Expr.any_and_eq_false`). -/
theorem resolveStatement_selectNoFrom (context : ResolveContext) (state : ResolveState) (value : Syntax.Expr)
    (text : String) (filter : Option Syntax.Expr) (expression : Resolved.Expr) (affinity : Option Affinity)
    (condition : Option Resolved.Expr) (notCall : value.isCall = false)
    (noAggregate : value.aggregateCalls.isEmpty = true)
    (operand : resolveOperand context.profile.dqsDml [] { later := [] } false value = .ok (expression, affinity))
    (plain : expression.any Resolved.Expr.isFallibleCall = false)
    (resolves : FilterResolves context.profile.dqsDml [] [] filter condition) :
    resolveStatement context state (.select [.expression value none text] none [] filter [] [] none none [] none false none) =
      .ok (.query (Resolved.Query.simple [] condition [.scalar expression] [(definedName [] value).getD text]) [], state) := by
  have simple : (Syntax.Subquery.mk [.expression value none text] none [] filter [] [] none none none none false none).Simple :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simpa using noAggregate⟩
  have result := resolveStatement_select_simple context state
    (Syntax.Subquery.mk [.expression value none text] none [] filter [] [] none none none none false none)
    simple rfl [] [] _ condition [] (resolveSources_none state.catalog) (by simp [starIssue])
    (resolveColumns_scalar context.profile.dqsDml [] { later := [] } value text expression affinity notCall operand)
    (by simpa [resultAliases] using resolves) (resolvePendingSources_nil _ _)
    (by simpa [Resolved.Expr.isFallibleCall] using Resolved.Expr.any_and_eq_false _ _ expression plain)
  simpa using result

end Belay.Sqlite.Model
