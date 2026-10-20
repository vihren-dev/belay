import Belay.Sqlite.Resolution.Values
import Belay.Sqlite.Resolution.MergedNames
import Belay.Sqlite.Resolution.ExprForms
import Belay.Sqlite.Resolution.SyntaxScope
import Belay.Sqlite.ExprEval
import Belay.Sqlite.Resolution.ExprAny
import Belay.Sqlite.ClockReads

set_option doc.verso true

/-! Resolution of the expressions of a query (ADR 0012, slice 1): names become
column positions, and the affinity rules of a comparison are checked. A
comparison whose affinity rule would convert a literal or the values of a column
is a model restriction, so that evaluation compares the stored values as they
are. -/

namespace Belay.Sqlite

mutual
/-- Resolve an expression over the sources in scope. An unqualified identifier is the
operand of its name ({name}`Scope.resolveName`, {name}`Scope.nameOperand`): one column,
or the coalesce of the columns that full joins merged; two columns that no join merged
are SQLite's {lit}`ambiguous column name: %s`. With none: a rowid name
({name}`rowidName`) is a model restriction when a table is in scope, because SQLite reads
the rowid; a name written in double quotes is a string literal when {lit}`dqs` is on;
an unquoted {lit}`TRUE` or {lit}`FALSE` is the integer 1 or 0; else it is SQLite's
{lit}`no such column: %s`, also for {lit}`[true]`, which only quotes. A qualified name {lit}`x.c` is column
{lit}`c` of the sources named {lit}`x` ({name}`Scope.resolveQualified`): one column, the
coalesce of merged columns, {lit}`ambiguous column name: x.c`, else
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
      else if quote == .double && dqs then .ok (.literal (.text name.bytes), none)
      else if quote == .none && booleanKeywordName name then
        .ok (.literal (.integer (if name.isKeyword (bytes! "true") then 1 else 0)), none)
      else .error (.prepare (.noSuchColumn name))
    | .ambiguous => .error (.prepare (.ambiguousColumn name))
  | .qualified source column => match scope.resolveQualified source column with
    | .found _ reads => .ok (scope.nameOperand reads)
    | .missing =>
      if rowidName column && scope.hasSource source then .error (.restriction [] .rowidName)
      else .error (.prepare (.noSuchColumn ⟨source.bytes ++ [46] ++ column.bytes⟩))
    | .ambiguous => .error (.prepare (.ambiguousColumn ⟨source.bytes ++ [46] ++ column.bytes⟩))
  | .compare operator left right => do
    let a ← (resolveOperand dqs scope misuse left).mapError (·.under [1])
    let b ← (resolveOperand dqs scope misuse right).mapError (·.under [2])
    if truthTest operator right b.1 then
      -- x IS [NOT] TRUE is (NOT NOT x) IS [NOT] 1, and x IS [NOT] FALSE is (NOT x) IS [NOT] 1.
      let tested := if b.1.literal? == some (.integer 1) then .not (.not a.1) else .not a.1
      .ok (.compare operator none tested (.literal (.integer 1)), none)
    else .ok (.compare operator (comparisonAffinity a.2 b.2) a.1 b.1, none)
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
