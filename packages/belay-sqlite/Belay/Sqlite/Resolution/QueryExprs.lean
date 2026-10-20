import Belay.Sqlite.Resolution.Values
import Belay.Sqlite.Resolution.MergedNames
import Belay.Sqlite.Resolution.FunctionCalls
import Belay.Sqlite.Resolution.SyntaxScope
import Belay.Sqlite.ExprEval
import Belay.Sqlite.Resolution.ExprAny
import Belay.Sqlite.ClockReads
import Belay.Sqlite.Resolution.Collations
import Belay.Sqlite.Resolution.SubqueryShapes

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
({name}`rowidName`) is a model restriction when a source with a rowid is in scope
({name}`ScopeSource.hasRowid`), because SQLite reads the rowid; a name written in double quotes is a string literal when {lit}`dqs` is on;
an unquoted {lit}`TRUE` or {lit}`FALSE` is the integer 1 or 0; else it is SQLite's
{lit}`no such column: %s`, also for {lit}`[true]`, which only quotes. A qualified name {lit}`x.c` is column
{lit}`c` of the sources named {lit}`x` ({name}`Scope.resolveQualified`): one column, the
coalesce of merged columns, {lit}`ambiguous column name: x.c`, else
{lit}`no such column: x.c`. The operands of {lit}`AND`, {lit}`OR` and {lit}`NOT` must be
conditions. An aggregate gives {name}`aggregateIssue`. A numeric literal has the value of
{name}`queryNumeric`; unary minus of another expression is {lit}`0 - operand` and unary
plus keeps the value without its affinity, as SQLite generates them; a {lit}`CAST` has
the affinity of its type name. A call resolves its arguments first, then is {name}`callOperand`, as SQLite
reports the errors of the arguments before those of the function; {lit}`name(*)` other than
{lit}`count(*)` is {name}`starCallIssue`. The issue path of argument {lit}`k` is
{lit}`[1, k]`. A comparison compares under {name}`comparisonCollation`. {lit}`x COLLATE c`
is the resolved {lit}`x`, whose collation the expression that uses it decides; a name
{lit}`c` other than {lit}`BINARY`, {lit}`NOCASE` and {lit}`RTRIM` is
{name}`RestrictionKind.unknownCollation`. A subquery form names a subquery that resolution
resolved before ({name}`SubqueryShapes.find`), else it is {name}`RestrictionKind.subqueryHere`; a
scalar subquery has the affinity of its result column, {lit}`x IN (q)` compares under
{name}`comparisonAffinity` and {name}`inCollation`, and both need one result column, else SQLite's
{lit}`sub-select returns %d columns - expected 1`. An aggregate whose arguments read a cell
of a query around the current one is {name}`RestrictionKind.outerAggregate`. -/
def resolveOperand (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (misuse : Bool) :
    Syntax.Expr → Except ValueIssue Operand
  | .identifier name quote => match scope.resolveName name with
    | .found _ reads => .ok (scope.nameOperand reads)
    | .missing =>
      if rowidName name && scope.any (·.hasRowid) then .error (.restriction [] .rowidName)
      else if quote == .double && dqs then .ok (.literal (.text name.bytes), none)
      else if quote == .none && booleanKeywordName name then
        .ok (.literal (.integer (if name.isKeyword (bytes! "true") then 1 else 0)), none)
      else .error (.prepare (.noSuchColumn name))
    | .ambiguous => .error (.prepare (.ambiguousColumn name))
  | .qualified source column => match scope.resolveQualified source column with
    | .found _ reads => .ok (scope.nameOperand reads)
    | .missing =>
      if rowidName column && scope.rowidSource source then .error (.restriction [] .rowidName)
      else .error (.prepare (.noSuchColumn ⟨source.bytes ++ [46] ++ column.bytes⟩))
    | .ambiguous => .error (.prepare (.ambiguousColumn ⟨source.bytes ++ [46] ++ column.bytes⟩))
  | .compare operator left right => do
    let a ← (resolveOperand dqs scope shapes misuse left).mapError (·.under [1])
    let b ← (resolveOperand dqs scope shapes misuse right).mapError (·.under [2])
    if truthTest operator right b.1 then
      -- x IS [NOT] TRUE is (NOT NOT x) IS [NOT] 1, and x IS [NOT] FALSE is (NOT x) IS [NOT] 1.
      let tested := if b.1.literal? == some (.integer 1) then .not (.not a.1) else .not a.1
      .ok (.compare operator none tested (.literal (.integer 1)), none)
    else .ok (.compare operator (comparisonAffinity a.2 b.2) a.1 b.1 (comparisonCollation scope left right), none)
  | .collate operand name => do
    let resolved ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    if (Collation.named? name).isNone then .error (.restriction [] .unknownCollation) else .ok resolved
  | .and left right => do
    let a ← condition [0] (resolveOperand dqs scope shapes misuse left)
    let b ← condition [1] (resolveOperand dqs scope shapes misuse right)
    .ok (.and a b, none)
  | .or left right => do
    let a ← condition [0] (resolveOperand dqs scope shapes misuse left)
    let b ← condition [1] (resolveOperand dqs scope shapes misuse right)
    .ok (.or a b, none)
  | .not operand => do
    let a ← condition [0] (resolveOperand dqs scope shapes misuse operand)
    .ok (.not a, none)
  | .isNull operand negated => do
    let a ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    .ok (.isNull a.1 negated, none)
  | .arithmetic operator left right => do
    let a ← (resolveOperand dqs scope shapes misuse left).mapError (·.under [1])
    let b ← (resolveOperand dqs scope shapes misuse right).mapError (·.under [2])
    .ok (.arithmetic operator a.1 b.1, none)
  | .cast operand typeName => do
    let a ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    let affinity := affinityOf (some typeName)
    .ok (.cast affinity a.1, some affinity)
  | .numeric text => (queryNumeric text false).map fun value => (.literal value, none)
  | .negate (.numeric text) => (queryNumeric text true).map fun value => (.literal value, none)
  | .negate operand => do
    let a ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    .ok (.arithmetic .subtract (.literal (.integer 0)) a.1, none)
  | .positive operand => do
    let a ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    .ok (a.1, none)
  | .call name arguments => do
    let resolved ← resolveArguments dqs scope shapes misuse 0 arguments
    if aggregateCall (.call name arguments) && resolved.readsUnder shapes shapes.outer then
      throw (.restriction [] .outerAggregate)
    callOperand scope misuse name arguments resolved
  | call@(.callStar name) => .error (if aggregateCall call then aggregateIssue misuse name else starCallIssue name)
  | .null => .ok (.literal .null, none)
  | .string bytes => .ok (.literal (.text bytes), none)
  | .blob bytes => .ok (.literal (.blob bytes), none)
  | .currentTime keyword => .ok (.now (timeKeywordNamed keyword), none)
  | .exists index => match shapes.find index with
    | some _ => .ok (.exists index, none)
    | none => .error (.restriction [] .subqueryHere)
  | .subquery index => match shapes.find index with
    | some shape =>
      if shape.columns == 1 then .ok (.subquery index, shape.affinity) else .error (.prepare (.subqueryColumns shape.columns))
    | none => .error (.restriction [] .subqueryHere)
  | .inQuery operand index negated => do
    let a ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    match shapes.find index with
    | some shape =>
      if shape.columns == 1 then
        .ok (.inQuery a.1 index (comparisonAffinity a.2 shape.affinity) (inCollation scope operand shape) negated, none)
      else .error (.prepare (.subqueryColumns shape.columns))
    | none => .error (.restriction [] .subqueryHere)

/-- Resolve the arguments of a call in written order ({name}`resolveOperand`), from
argument {lit}`index`; the issue of argument {lit}`k` is at {lit}`[1, k]`. -/
def resolveArguments (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (misuse : Bool) (index : Nat) :
    List Syntax.Expr → Except ValueIssue Resolved.Arguments
  | [] => .ok .nil
  | argument :: rest => do
    let a ← (resolveOperand dqs scope shapes misuse argument).mapError (·.under [1, index])
    let tail ← resolveArguments dqs scope shapes misuse (index + 1) rest
    .ok (.cons a.1 tail)
end

end Belay.Sqlite
