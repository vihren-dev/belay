import Belay.Sqlite.Resolution.Values
import Belay.Sqlite.Resolution.MergedNames
import Belay.Sqlite.Resolution.Calls
import Belay.Sqlite.Resolution.SyntaxScope
import Belay.Sqlite.JsonFaults
import Belay.Sqlite.ClockSubstitution

set_option doc.verso true

/-! Resolution of the expressions of a query (ADR 0012, slice 1): names become
column positions, and the affinity rules of a comparison are checked. A
comparison whose affinity rule would convert a literal or the values of a column
is a model restriction, so that evaluation compares the stored values as they
are. -/

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

mutual
/-- Resolve an expression over the sources in scope. An unqualified identifier is the
operand of its name ({name}`Scope.resolveName`, {name}`Scope.nameOperand`): one column,
or the coalesce of the columns that full joins merged; two columns that no join merged
are SQLite's {lit}`ambiguous column name: %s`. With none: a rowid name
({name}`rowidName`) is a model restriction when a table is in scope, because SQLite reads
the rowid; a name written in double quotes is a string literal when {lit}`dqs` is on;
an unquoted {lit}`TRUE` or {lit}`FALSE` is the integer 1 or 0; else it is SQLite's
{lit}`no such column: %s`, also for {lit}`[true]`, which only quotes. A qualified name {lit}`x.c` is column
{lit}`c` of the source named {lit}`x` ({name}`Scope.qualified`), else
{lit}`no such column: x.c`. The operands of {lit}`AND`, {lit}`OR` and {lit}`NOT` must be
conditions. An aggregate gives {name}`aggregateIssue`. A numeric literal has the value of
{name}`queryNumeric`; unary minus of another expression is {lit}`0 - operand` and unary
plus keeps the value without its affinity, as SQLite generates them; a {lit}`CAST` has
the affinity of its type name. A call keeps the checks that SQLite makes by its number of
arguments: without arguments only a date and time function; with one argument a JSON or
date and time function over its resolved argument, else an aggregate's issue or
{name}`callIssue`; with two or more {lit}`COALESCE`, a JSON or a date and time function over
its resolved arguments, else {name}`pairIssue`. The issue path of argument {lit}`k` is
{lit}`[1, k]`. -/
def resolveOperand (dqs : Bool) (scope : Scope) (misuse : Bool) : Syntax.Expr → Except ValueIssue Operand
  | .identifier name quote => match scope.resolveName name with
    | .found _ reads => .ok (scope.nameOperand reads)
    | .missing =>
      if rowidName name && !scope.isEmpty then .error (.restriction [] .rowidName)
      else if quote == .double && dqs then .ok (.literal (.text name.toUTF8.toList), none)
      else if quote == .none && booleanKeywordName name then
        .ok (.literal (.integer (if normalizeIdentifier name == "true" then 1 else 0)), none)
      else .error (.prepare (.noSuchColumn name))
    | .ambiguous => .error (.prepare (.ambiguousColumn name))
  | .qualified source column => match scope.qualified source column with
    | some position => .ok (.column position, (scope.columns[position]?.map CatalogColumn.affinity))
    | none =>
      if rowidName column && (scope.source? source).isSome then .error (.restriction [] .rowidName)
      else .error (.prepare (.noSuchColumn s!"{source}.{column}"))
  | .compare operator left right => do
    let a ← (resolveOperand dqs scope misuse left).mapError (·.under [1])
    let b ← (resolveOperand dqs scope misuse right).mapError (·.under [2])
    match affinityIssue a b with
    | some (path, reason) => .error (.restriction (path.map (· + 1)) reason)
    | none => .ok (.compare operator a.1 b.1, none)
  | .and left right => do
    let a ← condition [0] (resolveOperand dqs scope misuse left)
    let b ← condition [1] (resolveOperand dqs scope misuse right)
    .ok (.and a b, none)
  | .or left right => do
    let a ← condition [0] (resolveOperand dqs scope misuse left)
    let b ← condition [1] (resolveOperand dqs scope misuse right)
    .ok (.or a b, none)
  | .not operand => do
    let a ← condition [0] (resolveOperand dqs scope misuse operand)
    .ok (.not a, none)
  | .isNull operand negated => do
    let a ← (resolveOperand dqs scope misuse operand).mapError (·.under [0])
    .ok (.isNull a.1 negated, none)
  | .arithmetic operator left right => do
    let a ← (resolveOperand dqs scope misuse left).mapError (·.under [1])
    let b ← (resolveOperand dqs scope misuse right).mapError (·.under [2])
    .ok (.arithmetic operator a.1 b.1, none)
  | .cast operand typeName => do
    let a ← (resolveOperand dqs scope misuse operand).mapError (·.under [0])
    let affinity := affinityOf (some typeName)
    .ok (.cast affinity a.1, some affinity)
  | .numeric text => (queryNumeric text false).map fun value => (.literal value, none)
  | .negate (.numeric text) => (queryNumeric text true).map fun value => (.literal value, none)
  | .negate operand => do
    let a ← (resolveOperand dqs scope misuse operand).mapError (·.under [0])
    .ok (.arithmetic .subtract (.literal (.integer 0)) a.1, none)
  | .positive operand => do
    let a ← (resolveOperand dqs scope misuse operand).mapError (·.under [0])
    .ok (a.1, none)
  | .call name arguments => match arguments with
    | [] => match dateFunctionNamed name with
      | some function => dateCall function .nil
      | none => .error (callIssue name)
    | [_] =>
      if (jsonFunctionNamed name).isSome || (dateFunctionNamed name).isSome then do
        let resolved ← resolveArguments dqs scope misuse 0 arguments
        functionCall name resolved (callIssue name)
      else .error (if (aggregateNamed name).isSome then aggregateIssue misuse name else callIssue name)
    | _ :: _ :: _ =>
      if normalizeIdentifier name == "coalesce" || scalarFunctionName name then do
        let resolved ← resolveArguments dqs scope misuse 0 arguments
        functionCall name resolved (pairIssue name)
      else .error (pairIssue name)
  | call@(.callStar name) => .error (if aggregateCall call then aggregateIssue misuse name else callIssue name)
  | .null => .ok (.literal .null, none)
  | .string bytes => .ok (.literal (.text bytes), none)
  | .blob bytes => .ok (.literal (.blob bytes), none)
  | .currentTime keyword => .ok (.now (timeKeywordNamed keyword), none)

/-- Resolve the arguments of a call in written order ({name}`resolveOperand`), from
argument {lit}`index`; the issue of argument {lit}`k` is at {lit}`[1, k]`. -/
def resolveArguments (dqs : Bool) (scope : Scope) (misuse : Bool) (index : Nat) :
    List Syntax.Expr → Except ValueIssue Resolved.Arguments
  | [] => .ok .nil
  | argument :: rest => do
    let a ← (resolveOperand dqs scope misuse argument).mapError (·.under [1, index])
    let tail ← resolveArguments dqs scope misuse (index + 1) rest
    .ok (.cons a.1 tail)
end

end Belay.Sqlite
