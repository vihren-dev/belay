import Belay.Sqlite.Resolution.Values
import Belay.Sqlite.Resolution.MergedNames
import Belay.Sqlite.Resolution.QueryAffinity
import Belay.Sqlite.QueryEval

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
  | .column _ | .literal _ | .coalesce .. => false

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
  | .call name _ => (aggregateNamed name).isSome
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .identifier .. | .negate _ | .positive _
  | .equals .. | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic .. | .cast .. | .callPair ..
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

/-- Whether an expression names a result column alias: an identifier that names no
column in scope but, after ASCII folding, is one of {lit}`aliases`. SQLite
resolves such a name in {lit}`WHERE` and inside {lit}`ORDER BY` expressions to the
aliased result expression, before the double-quoted string fallback. -/
def namesAlias (scope : Scope) (aliases : List String) : Syntax.Expr → Bool
  | .identifier name _ => (scope.matches name).isEmpty &&
      aliases.any (normalizeIdentifier · == normalizeIdentifier name)
  | .equals left right | .compare _ left right | .and left right | .or left right =>
    namesAlias scope aliases left || namesAlias scope aliases right
  | .arithmetic _ left right | .callPair _ left right => namesAlias scope aliases left || namesAlias scope aliases right
  | .not operand | .isNull operand _ | .call _ operand | .negate operand | .positive operand | .cast operand _ =>
    namesAlias scope aliases operand
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .callStar _ | .qualified .. => false

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

/-- Resolve an expression over the sources in scope. An unqualified identifier is the
operand of its name ({name}`Scope.resolveName`, {name}`Scope.nameOperand`): one column,
or the coalesce of the columns that full joins merged; two columns that no join merged
are SQLite's {lit}`ambiguous column name: %s`. With none: a rowid name
({name}`rowidName`) is a model restriction when a table is in scope, because SQLite reads
the rowid; a name written in double quotes is a string literal when {lit}`dqs` is on;
else it is SQLite's {lit}`no such column: %s`. A qualified name {lit}`x.c` is column
{lit}`c` of the source named {lit}`x` ({name}`Scope.qualified`), else
{lit}`no such column: x.c`. The operands of {lit}`AND`, {lit}`OR` and {lit}`NOT` must be
conditions. An aggregate gives {name}`aggregateIssue`. A numeric literal has the value of
{name}`queryNumeric`; unary minus of another expression is {lit}`0 - operand` and unary
plus keeps the value without its affinity, as SQLite generates them; a {lit}`CAST` has
the affinity of its type name. -/
def resolveOperand (dqs : Bool) (scope : Scope) (misuse : Bool) : Syntax.Expr → Except ValueIssue Operand
  | .identifier name doubleQuoted => match scope.resolveName name with
    | .found _ reads => .ok (scope.nameOperand reads)
    | .missing =>
      if rowidName name && !scope.isEmpty then .error (.restriction [] .rowidName)
      else if doubleQuoted && dqs then .ok (.literal (.text name.toUTF8.toList), none)
      else .error (.prepare (.noSuchColumn name))
    | .ambiguous => .error (.prepare (.ambiguousColumn name))
  | .qualified source column => match scope.qualified source column with
    | some position => .ok (.column position, (scope.columns[position]?.map CatalogColumn.affinity))
    | none =>
      if rowidName column && (scope.source? source).isSome then .error (.restriction [] .rowidName)
      else .error (.prepare (.noSuchColumn s!"{source}.{column}"))
  | .equals left right => do
    let a ← (resolveOperand dqs scope misuse left).mapError (·.under [0])
    let b ← (resolveOperand dqs scope misuse right).mapError (·.under [1])
    match affinityIssue a b with
    | some (path, reason) => .error (.restriction path reason)
    | none => .ok (.compare .eq a.1 b.1, none)
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
  | .callPair name first rest =>
    if normalizeIdentifier name == "coalesce" then do
      let a ← (resolveOperand dqs scope misuse first).mapError (·.under [1])
      let b ← (resolveOperand dqs scope misuse rest).mapError (·.under [2])
      .ok (.coalesce a.1 b.1, none)
    else .error (pairIssue name)
  | .numeric text => (queryNumeric text false).map fun value => (.literal value, none)
  | .negate (.numeric text) => (queryNumeric text true).map fun value => (.literal value, none)
  | .negate operand => do
    let a ← (resolveOperand dqs scope misuse operand).mapError (·.under [0])
    .ok (.arithmetic .subtract (.literal (.integer 0)) a.1, none)
  | .positive operand => do
    let a ← (resolveOperand dqs scope misuse operand).mapError (·.under [0])
    .ok (a.1, none)
  | call@(.callStar name) | call@(.call name _) =>
    .error (if aggregateCall call then aggregateIssue misuse name else callIssue name)
  | .null => .ok (.literal .null, none)
  | .string bytes => .ok (.literal (.text bytes), none)
  | .blob bytes => .ok (.literal (.blob bytes), none)
  | .currentTime _ => .error (.restriction [] .timeValue)

/-- Whether an expression names a column in scope: an identifier with the folded name of
a column, or a qualified name of one, anywhere in the expression. A write value that names a column
depends on the row. -/
def mentionsColumn (scope : Scope) : Syntax.Expr → Bool
  | .identifier name _ => !(scope.matches name).isEmpty
  | .qualified source column => (scope.qualified source column).isSome
  | .equals left right | .compare _ left right | .and left right | .or left right
  | .arithmetic _ left right | .callPair _ left right => mentionsColumn scope left || mentionsColumn scope right
  | .not operand | .isNull operand _ | .call _ operand | .negate operand | .positive operand | .cast operand _ =>
    mentionsColumn scope operand
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .callStar _ => false

/-- The value of a constant expression in a write (ADR 0012, slice 3a): the expression
resolved as a query expression with no column in scope and an aggregate as SQLite's
{lit}`misuse of aggregate function`, then evaluated. So {lit}`1 + 2` is 3 and
{lit}`CAST('7' AS INTEGER)` is 7; an identifier, a rowid name included, is a
double-quoted string or {lit}`no such column`, as in a {lit}`VALUES` row, where no table
is in scope. -/
def constantValue (dqs : Bool) (expression : Syntax.Expr) : Except ValueIssue Value :=
  (resolveOperand dqs [] true expression).map fun operand => operand.1.eval []

end Belay.Sqlite
