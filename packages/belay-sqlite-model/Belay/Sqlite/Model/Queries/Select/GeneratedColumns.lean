import Belay.Sqlite.Model.Queries.Select.TableChecks
import Belay.Sqlite.Model.Queries.Select.NondeterministicCalls

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The issue of a resolved generated expression, or none: a {lit}`CURRENT_TIME`,
{lit}`CURRENT_DATE` or {lit}`CURRENT_TIMESTAMP` is SQLite's
{name}`ExprError.nondeterministicGenerated`; a date and time function, whose {lit}`'now'`
SQLite refuses only when it writes a row, and a JSON function or another function whose
evaluation can fail ({name}`Resolved.Expr.isFallibleCall`), are
{name}`RestrictionKind.generatedFunction`. -/
def generatedIssue (resolved : Resolved.Expr) : Option ValueIssue :=
  if resolved.any Resolved.Expr.isNow then some (.prepare .nondeterministicGenerated)
  else if resolved.any Resolved.Expr.isDateCall || resolved.any Resolved.Expr.isFallibleCall then
    some (.restriction [] .generatedFunction)
  else none

/-- One generated expression over the scope: a parameter is
{name}`ExprError.parameterInGenerated` in SQLite's order ({name}`prohibitParameter`); a qualified name is
{name}`ExprError.qualifiedGenerated`; a call of a function that is not deterministic is
{name}`ExprError.nondeterministicGenerated` where SQLite's walk finds no other error
({name}`prohibitNondeterministic`); else the resolved operand and its {name}`generatedIssue`. -/
def resolveGeneratedExpression (dqs : Bool) (scope : Scope) (expression : Syntax.Expr) :
    Except ValueIssue Resolved.Expr := do
  prohibitParameter dqs scope .parameterInGenerated expression
  if expression.hasQualifiedName then throw (.prepare .qualifiedGenerated)
  prohibitNondeterministic dqs scope .nondeterministicGenerated expression
  let (resolved, _) ← resolveOperand dqs scope {} true expression
  match generatedIssue resolved with
  | some issue => .error issue
  | none => .ok resolved

end Belay.Sqlite.Model
