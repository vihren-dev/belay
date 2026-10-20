import Belay.Sqlite.Resolution.Calls
import Belay.Sqlite.Resolution.FunctionCatalog

set_option doc.verso true

/-! Forms that query expression resolution decides before it resolves an operand: which
calls are aggregates and the issues of calls the model does not evaluate, SQLite's truth
test {lit}`x IS TRUE`, and conditions. -/

namespace Belay.Sqlite

/-- The issue of an aggregate where only a row value can be: SQLite's
{lit}`misuse of aggregate function` when {lit}`misuse` is true (in {lit}`WHERE`, or
inside another aggregate), else a model restriction (inside an expression of a
result column). -/
def aggregateIssue (misuse : Bool) (function : String) : ValueIssue :=
  if misuse then .prepare (.misuseOfAggregate function)
  else .restriction [] .aggregateInExpression

/-- The aggregate of one operand that a function name names, after ASCII folding:
{lit}`count`, {lit}`min`, {lit}`max`, {lit}`sum`, {lit}`avg`, {lit}`json_group_array`,
{lit}`jsonb_group_array`, {lit}`group_concat` or {lit}`total`. -/
def aggregateNamed (name : String) : Option (Resolved.Expr → Resolved.Aggregate) :=
  match normalizeIdentifier name with
  | "count" => some .count
  | "min" => some .min
  | "max" => some .max
  | "sum" => some .sum
  | "avg" => some .avg
  | "json_group_array" => some (.jsonGroupArray · false)
  | "jsonb_group_array" => some (.jsonGroupArray · true)
  | "group_concat" => some (.groupConcat · none)
  | "total" => some .total
  | _ => none

/-- The aggregate of two operands that a function name names, after ASCII folding:
{lit}`json_group_object`, {lit}`jsonb_group_object`, and {lit}`group_concat` and {lit}`string_agg`
with a separator. -/
def pairAggregateNamed (name : String) : Option (Resolved.Expr → Resolved.Expr → Resolved.Aggregate) :=
  match normalizeIdentifier name with
  | "json_group_object" => some (.jsonGroupObject · · false)
  | "jsonb_group_object" => some (.jsonGroupObject · · true)
  | "group_concat" | "string_agg" => some fun operand separator => .groupConcat operand (some separator)
  | _ => none

/-- Whether an aggregate writes its operand as a JSON value, so that the JSON subtype of the
operand matters: {lit}`json_group_array` and {lit}`json_group_object`. -/
def Resolved.Aggregate.writesJson : Resolved.Aggregate → Bool
  | .jsonGroupArray .. | .jsonGroupObject .. => true
  | .countRows | .count _ | .min .. | .max .. | .sum _ | .avg _ | .groupConcat .. | .total _ => false

/-- Whether a call is an aggregate of the model: {lit}`count(*)`, or a named aggregate
of one operand ({name}`aggregateNamed`) or of two ({name}`pairAggregateNamed`). -/
def aggregateCall : Syntax.Expr → Bool
  | .callStar name => normalizeIdentifier name == "count"
  | .call name [_] => (aggregateNamed name).isSome
  | .call name [_, _] => (pairAggregateNamed name).isSome
  | .call _ [] | .call _ (_ :: _ :: _ :: _) => false
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .identifier .. | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic .. | .cast ..
  | .qualified .. | .collate .. | .exists _ | .inQuery .. | .subquery _ => false

/-- The restriction for a function call that the model does not evaluate. -/
def unmodeledFunction : ValueIssue :=
  .restriction [] .unmodeledFunction

/-- The issue of a call where the model does not evaluate calls, such as a {lit}`GROUP BY`
term: SQLite's {lit}`no such function` for a name that names no function of the catalog
({name}`builtinFunction?`), else {name}`unmodeledFunction`. -/
def callIssue (name : String) : ValueIssue :=
  if (builtinFunction? (normalizeIdentifier name)).isNone then .prepare (.noSuchFunction name) else unmodeledFunction

/-- Whether an expression as written is an unquoted {lit}`TRUE` or {lit}`FALSE`. -/
def Syntax.Expr.unquotedBoolean : Syntax.Expr → Bool
  | .identifier name quote => quote == .none && booleanKeywordName name
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .qualified .. | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast ..
  | .collate .. | .exists _ | .inQuery .. | .subquery _ => false

/-- Whether a comparison is SQLite's truth test: {lit}`IS` or {lit}`IS NOT` whose right
operand is an unquoted {lit}`TRUE` or {lit}`FALSE` that names no column, so it resolved to
its keyword value. SQLite then tests the truth of the left operand ({lit}`TK_TRUTH`):
{lit}`2 IS TRUE` is 1, although {lit}`2 IS 1` is 0. Resolution gives the test as
{lit}`(NOT NOT x) IS 1` for TRUE and {lit}`(NOT x) IS 1` for FALSE, with {lit}`IS NOT` for the
negated test. -/
def truthTest (operator : Comparison) (right : Syntax.Expr) (resolved : Resolved.Expr) : Bool :=
  (operator == .is || operator == .isNot) && right.unquotedBoolean && resolved.literal?.isSome

/-- The restriction for a result column alias inside an expression. -/
def aliasInExpression : ValueIssue :=
  .restriction [] .aliasInExpression

/-- A condition: the resolved expression of an operand, whose truth SQLite takes
({lit}`truthy`), with the issue of the operand under {lit}`path`. Every value is a
condition. -/
def condition (path : List Nat) : Except ValueIssue Operand → Except ValueIssue Resolved.Expr
  | .ok (expression, _) => .ok expression
  | .error issue => .error (issue.under path)

end Belay.Sqlite
