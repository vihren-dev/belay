import Belay.Sqlite.Model.Resolution.OperandForms

set_option doc.verso true

/-! Resolution of the expressions of a query (ADR 0012, slice 1), with the name trace: names become
column positions, and each comparison keeps the affinity and collation that evaluation applies. Each
name and each comparison that the resolver decides is recorded as it is decided. -/

namespace Belay.Sqlite.Model

mutual
/-- Resolve an expression over the sources in scope, recording the occurrences that it decides.
The name-trace form of {lit}`resolveOperand`, which is its projection. An unqualified identifier is the
operand of its name ({name}`Scope.resolveName`, {name}`Scope.nameOperand`): one column,
or the coalesce of the columns that full joins merged; two columns that no join merged
are SQLite's {lit}`ambiguous column name: %s`. With none: a rowid name
({name}`rowidName`) is a model restriction when a source with visible names and a rowid is in scope
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
{name}`comparisonAffinity` and {name}`inCollation`, and both read one result column
({name}`SubqueryShapes.column`). An aggregate whose arguments read a cell
of a query around the current one is {name}`RestrictionKind.outerAggregate`. {lit}`x IN (list)`
compares under the affinity and the collation of {lit}`x`, but a list of one constant value with an
explicit collation is {lit}`x = +c`, as SQLite's parser reads it; {lit}`x BETWEEN a AND b` is
{lit}`x >= a AND x <= b`; {lit}`CASE` is {lit}`iif` of its operands ({lit}`resolveCase`); and
{lit}`x || y` is the scalar function of the operator; a listed aggregate call
({name}`SubqueryShapes.aggregates`) that is no misuse names its aggregate by index; {lit}`RAISE`
outside a trigger's statements is {name}`ExprError.raiseOutsideTrigger`. -/
def resolveOperandTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (misuse : Bool) :
    Syntax.Expr → Traced ValueIssue Operand
  | .identifier name quote => identifierTraced dqs scope name quote
  | .qualified source column schema => qualifiedTraced scope source column schema
  | .compare operator left right => do
    let a ← (resolveOperandTraced dqs scope shapes misuse left).under [1]
    let b ← (resolveOperandTraced dqs scope shapes misuse right).under [2]
    compareTraced scope operator left right a b
  | .collate operand name => do
    let resolved ← (resolveOperandTraced dqs scope shapes misuse operand).under [0]
    if (Collation.named? name).isNone then throw (.restriction [] .unknownCollation) else pure resolved
  | .and left right => do
    let a ← Traced.condition [0] (resolveOperandTraced dqs scope shapes misuse left)
    let b ← Traced.condition [1] (resolveOperandTraced dqs scope shapes misuse right)
    pure (.and a b, none)
  | .or left right => do
    let a ← Traced.condition [0] (resolveOperandTraced dqs scope shapes misuse left)
    let b ← Traced.condition [1] (resolveOperandTraced dqs scope shapes misuse right)
    pure (.or a b, none)
  | .not operand => do
    let a ← Traced.condition [0] (resolveOperandTraced dqs scope shapes misuse operand)
    pure (.not a, none)
  | .isNull operand negated => do
    let a ← (resolveOperandTraced dqs scope shapes misuse operand).under [0]
    pure (.isNull a.1 negated, none)
  | .arithmetic operator left right => do
    let a ← (resolveOperandTraced dqs scope shapes misuse left).under [1]
    let b ← (resolveOperandTraced dqs scope shapes misuse right).under [2]
    pure (.arithmetic operator a.1 b.1, none)
  | .cast operand typeName => do
    let a ← (resolveOperandTraced dqs scope shapes misuse operand).under [0]
    let affinity := affinityOf (some typeName)
    pure (.cast affinity a.1, some affinity)
  | .numeric text => Traced.lift ((queryNumeric text false).map fun value => (.literal value, none))
  | .negate (.numeric text) => Traced.lift ((queryNumeric text true).map fun value => (.literal value, none))
  | .negate operand => do
    let a ← (resolveOperandTraced dqs scope shapes misuse operand).under [0]
    pure (.arithmetic .subtract (.literal (.integer 0)) a.1, none)
  | .positive operand => do
    let a ← (resolveOperandTraced dqs scope shapes misuse operand).under [0]
    pure (a.1, none)
  | .call name arguments => do
    let resolved ← resolveArgumentsTraced dqs scope shapes misuse 0 arguments
    if aggregateCall (.call name arguments) && resolved.readsUnder shapes shapes.outer then
      throw (.restriction [] .outerAggregate)
    match misuse, (Syntax.Expr.call name arguments).indexIn shapes.aggregates with
    | false, some index => pure (.aggregateValue index, none)
    | _, _ => Traced.lift (callOperand scope misuse name arguments resolved)
  | call@(.callStar name) => match misuse, call.indexIn shapes.aggregates with
    | false, some index => pure (.aggregateValue index, none)
    | _, _ => throw (if aggregateCall call then aggregateIssue misuse name else starCallIssue name)
  | .null => pure (.literal .null, none)
  | .string bytes => pure (.literal (.text bytes), none)
  | .blob bytes => pure (.literal (.blob bytes), none)
  | .currentTime keyword => pure (.now (timeKeywordNamed keyword), none)
  | .parameter number => pure (.parameter number, none)
  | .exists index => match shapes.find index with
    | some _ => pure (.exists index, none)
    | none => throw (.restriction [] .subqueryHere)
  | .subquery index => Traced.lift ((shapes.column index).map fun shape => (.subquery index, shape.affinity))
  | .inList operand values negated => do
    let a ← (resolveOperandTraced dqs scope shapes misuse operand).under [0]
    let resolved ← resolveArgumentsTraced dqs scope shapes misuse 0 values
    inListTraced scope shapes operand values negated a resolved
  | .between operand low high negated => do
    let a ← (resolveOperandTraced dqs scope shapes misuse operand).under [0]
    let l ← (resolveOperandTraced dqs scope shapes misuse low).under [1]
    let h ← (resolveOperandTraced dqs scope shapes misuse high).under [2]
    betweenTraced scope operand low high negated a l h
  | .caseOf operands hasBase => do
    let arguments ← resolveCaseTraced dqs scope shapes misuse hasBase none 0 operands
    pure (.scalar .iif arguments, none)
  | .concatenate left right => do
    let a ← (resolveOperandTraced dqs scope shapes misuse left).under [0]
    let b ← (resolveOperandTraced dqs scope shapes misuse right).under [1]
    pure (.scalar .pipes (.cons a.1 (.cons b.1 .nil)), none)
  | .raise .. => throw (.prepare .raiseOutsideTrigger)
  | .inQuery operand index negated => do
    let a ← (resolveOperandTraced dqs scope shapes misuse operand).under [0]
    let shape ← Traced.lift (shapes.column index)
    inQueryTraced scope operand index negated a shape

/-- Resolve the arguments of a call in written order ({name}`resolveOperandTraced`), from
argument {lit}`index`; the issue and the occurrences of argument {lit}`k` are at {lit}`[1, k]`. -/
def resolveArgumentsTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (misuse : Bool) (index : Nat) :
    List Syntax.Expr → Traced ValueIssue Resolved.Arguments
  | [] => pure .nil
  | argument :: rest => do
    let a ← (resolveOperandTraced dqs scope shapes misuse argument).under [1, index]
    let tail ← resolveArgumentsTraced dqs scope shapes misuse (index + 1) rest
    pure (.cons a.1 tail)

/-- Resolve the operands of {lit}`CASE` from operand {lit}`index` as the arguments of {lit}`iif`,
which gives SQLite's value of {lit}`CASE`: the base expression first when {lit}`needsBase`, which
is then {lit}`base` and not an argument; each {lit}`WHEN` value that is not the last operand,
compared with the base as {lit}`=` compares them ({name}`comparisonAffinity`,
{name}`comparisonCollation`) when there is a base, with a comparison occurrence at the value; every
other operand as it is. The issue and the occurrences of operand {lit}`k` are at {lit}`[0, k]`. -/
def resolveCaseTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (misuse : Bool) (needsBase : Bool)
    (base : Option (Syntax.Expr × Operand)) (index : Nat) :
    List Syntax.Expr → Traced ValueIssue Resolved.Arguments
  | [] => pure .nil
  | operand :: rest => do
    let resolved ← (resolveOperandTraced dqs scope shapes misuse operand).under [0, index]
    if needsBase then resolveCaseTraced dqs scope shapes misuse false (some (operand, resolved)) (index + 1) rest
    else
      let isWhen := (index - (if base.isSome then 1 else 0)) % 2 == 0 && !rest.isEmpty
      let item ← match base, isWhen with
        | some (written, value), true => caseWhenTraced scope [0, index] written value operand resolved
        | _, _ => pure resolved.1
      let tail ← resolveCaseTraced dqs scope shapes misuse false base (index + 1) rest
      pure (.cons item tail)
end

end Belay.Sqlite.Model
