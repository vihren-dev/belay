import Belay.Sqlite.Resolution.Calls

set_option doc.verso true

/-! Forms that query expression resolution decides before it resolves an operand: which
resolved expressions are conditions, which calls are aggregates and the issues of calls
the model does not evaluate, and SQLite's truth test {lit}`x IS TRUE`. -/

namespace Belay.Sqlite

/-- Whether a resolved expression gives a truth value without a text-to-number
conversion: a comparison, a logical operator, {lit}`IS NULL`, arithmetic, or a
{lit}`CAST` to INTEGER, REAL or NUMERIC, whose values are numbers or NULL. -/
def Resolved.Expr.isCondition : Resolved.Expr → Bool
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic .. => true
  | .cast affinity _ => numericAffinity affinity
  | .column _ | .literal _ | .coalesce .. | .json .. | .now _ | .date .. => false

/-- The issue of an aggregate where only a row value can be: SQLite's
{lit}`misuse of aggregate function` when {lit}`misuse` is true (in {lit}`WHERE`, or
inside another aggregate), else a model restriction (inside an expression of a
result column). -/
def aggregateIssue (misuse : Bool) (function : String) : ValueIssue :=
  if misuse then .prepare (.misuseOfAggregate function)
  else .restriction [] .aggregateInExpression

/-- The aggregate that a function name names, after ASCII folding: {lit}`count`,
{lit}`min`, {lit}`max`, {lit}`sum` or {lit}`avg` of one operand. -/
def aggregateNamed (name : String) : Option (Resolved.Expr → Resolved.Aggregate) :=
  match normalizeIdentifier name with
  | "count" => some .count
  | "min" => some .min
  | "max" => some .max
  | "sum" => some .sum
  | "avg" => some .avg
  | _ => none

/-- Whether a call is an aggregate of slice 1: {lit}`count(*)`, or a named aggregate
of one operand. -/
def aggregateCall : Syntax.Expr → Bool
  | .callStar name => normalizeIdentifier name == "count"
  | .call name [_] => (aggregateNamed name).isSome
  | .call _ [] | .call _ (_ :: _ :: _) => false
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .identifier .. | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic .. | .cast ..
  | .qualified .. => false

/-- The restriction for a function call that the model does not evaluate. -/
def unmodeledFunction : ValueIssue :=
  .restriction [] .unmodeledFunction

/-- The issue of a call with {lit}`*` or one argument that is not an aggregate:
SQLite's {lit}`wrong number of arguments` for {lit}`COALESCE`, which needs two or more
arguments; else {name}`unmodeledFunction`. -/
def callIssue (name : String) : ValueIssue :=
  if normalizeIdentifier name == "coalesce" then .prepare (.wrongArgumentCount name) else unmodeledFunction

/-- The issue of a call with two or more arguments that is not {lit}`COALESCE`: SQLite's
{lit}`wrong number of arguments` for {lit}`COUNT`, whose aggregate takes one argument;
else {name}`unmodeledFunction`. {lit}`MIN` and {lit}`MAX` with two or more arguments are
scalar functions, which the model does not evaluate. -/
def pairIssue (name : String) : ValueIssue :=
  if normalizeIdentifier name == "count" then .prepare (.wrongArgumentCount name) else unmodeledFunction

/-- Whether an expression as written is an unquoted {lit}`TRUE` or {lit}`FALSE`. -/
def Syntax.Expr.unquotedBoolean : Syntax.Expr → Bool
  | .identifier name quote => quote == .none && booleanKeywordName name
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .qualified .. | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast .. =>
    false

/-- Whether a comparison is SQLite's truth test: {lit}`IS` or {lit}`IS NOT` whose right
operand is an unquoted {lit}`TRUE` or {lit}`FALSE` that names no column, so it resolved to
its keyword value. SQLite then tests the truth of the left operand ({lit}`TK_TRUTH`):
{lit}`2 IS TRUE` is 1, although {lit}`2 IS 1` is 0. For a left operand whose value is 0, 1
or NULL ({name}`Resolved.Expr.isCondition`) the test equals the comparison with the keyword
value; resolution refuses any other left operand ({lit}`valueAsCondition`). -/
def truthTest (operator : Comparison) (right : Syntax.Expr) (resolved : Resolved.Expr) : Bool :=
  (operator == .is || operator == .isNot) && right.unquotedBoolean && resolved.literal?.isSome

/-- The restriction for a result column alias inside an expression. -/
def aliasInExpression : ValueIssue :=
  .restriction [] .aliasInExpression

/-- A condition, or a model restriction at {lit}`path` when the operand gives a
value instead of a truth value. -/
def condition (path : List Nat) : Except ValueIssue Operand → Except ValueIssue Resolved.Expr
  | .ok (expression, _) =>
    if expression.isCondition then .ok expression
    else .error (.restriction path .valueAsCondition)
  | .error issue => .error (issue.under path)

end Belay.Sqlite
