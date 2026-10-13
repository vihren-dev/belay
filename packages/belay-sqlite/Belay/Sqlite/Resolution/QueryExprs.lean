import Belay.Sqlite.Resolution.Writes
import Belay.Sqlite.Resolution.QueryForm

set_option doc.verso true

/-! Resolution of the expressions of a query (ADR 0012, slice 1): names become
column positions, and the affinity rules of a comparison are checked. A
comparison whose affinity rule would convert a literal or the values of a column
is a model restriction, so that evaluation compares the stored values as they
are. -/

namespace Belay.Sqlite

/-- A resolved operand and its affinity in a comparison: a column reference has
its column's affinity, every other expression has none. -/
abbrev Operand := Resolved.Expr × Option Affinity

/-- Whether an affinity is INTEGER, REAL or NUMERIC. -/
def numericAffinity : Affinity → Bool
  | .integer | .real | .numeric => true
  | .text | .blob => false

/-- Whether a resolved expression gives a truth value: a comparison, a logical
operator, or {lit}`IS NULL`. -/
def Resolved.Expr.isCondition : Resolved.Expr → Bool
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. => true
  | .column _ | .literal _ => false

/-- The literal value of a resolved expression, if it is a literal. -/
def Resolved.Expr.literal? : Resolved.Expr → Option Value
  | .literal value => some value
  | .column _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. => none

/-- Whether a value is TEXT. -/
def Value.isText : Value → Bool
  | .text _ => true
  | .null | .integer _ | .real _ | .blob _ => false

/-- Whether TEXT affinity keeps a value unchanged: NULL, TEXT or BLOB. -/
def Value.keepsText : Value → Bool
  | .null | .text _ | .blob _ => true
  | .integer _ | .real _ => false

/-- Why the affinity rule of a comparison would convert one operand, given the
affinity of the other: when the other operand has INTEGER, REAL or NUMERIC
affinity, a text literal or a column of another affinity would get NUMERIC
affinity (R-58138-64688); when the other operand is a TEXT column and this one has
no affinity, a value other than a NULL, text or blob literal would get TEXT
affinity (R-29161-32953). -/
def conversion (target : Operand) (other : Option Affinity) : Option String :=
  if other.any numericAffinity then
    match target.2 with
    | some affinity =>
      if numericAffinity affinity then none
      else some "a comparison of columns with different kinds of affinity is not modeled; compare columns with the same kind"
    | none =>
      if (target.1.literal?.map Value.isText).getD false then
        some "a text value compared with a numeric column would be converted to a number; write a number"
      else none
  else if other == some .text && target.2.isNone && !((target.1.literal?.map Value.keepsText).getD false) then
    some "a number compared with a TEXT column would be converted to text; write a text value"
  else none

/-- Why the affinity rule of a comparison would convert an operand, with the path of
that operand (R-10393-27560), checking the left operand first. -/
def affinityIssue (left right : Operand) : Option (List Nat × String) :=
  match conversion left right.2 with
  | some reason => some ([0], reason)
  | none => (conversion right left.2).map ([1], ·)

/-- The issue of an aggregate where only a row value can be: SQLite's
{lit}`misuse of aggregate function` when {lit}`misuse` is true (in {lit}`WHERE`, or
inside another aggregate), else a model restriction (inside an expression of a
result column). -/
def aggregateIssue (misuse : Bool) (function : String) : ValueIssue :=
  if misuse then .prepare (.misuseOfAggregate function)
  else .restriction [] "an aggregate inside an expression is not modeled; use the aggregate as a whole result column"

/-- The aggregate of slice 1 that a function name names, after ASCII folding:
{lit}`count`, {lit}`min` or {lit}`max` of one operand. -/
def aggregateNamed (name : String) : Option (Resolved.Expr → Resolved.Aggregate) :=
  match normalizeIdentifier name with
  | "count" => some .count
  | "min" => some .min
  | "max" => some .max
  | _ => none

/-- Whether a call is an aggregate of slice 1: {lit}`count(*)`, or a named aggregate
of one operand. -/
def aggregateCall : Syntax.Expr → Bool
  | .callStar name => normalizeIdentifier name == "count"
  | .call name _ => (aggregateNamed name).isSome
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .identifier .. | .negate _ | .positive _
  | .equals .. | .compare .. | .and .. | .or .. | .not _ | .isNull .. => false

/-- The restriction for a function call that slice 1 does not evaluate. -/
def unmodeledFunction : ValueIssue :=
  .restriction [] "only COUNT(*), and COUNT, MIN and MAX of one argument, are modeled as functions"

/-- Whether an expression names a result column alias: an identifier that names no
column of the table but, after ASCII folding, is one of {lit}`aliases`. SQLite
resolves such a name in {lit}`WHERE` and inside {lit}`ORDER BY` expressions to the
aliased result expression, before the double-quoted string fallback. -/
def namesAlias (columns : List CatalogColumn) (aliases : List String) : Syntax.Expr → Bool
  | .identifier name _ => (columnPosition columns name).isNone &&
      aliases.any (normalizeIdentifier · == normalizeIdentifier name)
  | .equals left right | .compare _ left right | .and left right | .or left right =>
    namesAlias columns aliases left || namesAlias columns aliases right
  | .not operand | .isNull operand _ | .call _ operand | .negate operand | .positive operand =>
    namesAlias columns aliases operand
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .callStar _ => false

/-- The restriction for a result column alias inside an expression. -/
def aliasInExpression : ValueIssue :=
  .restriction [] "a result column alias inside WHERE or an ORDER BY expression is not modeled; write the column expression"

/-- A condition, or a model restriction at {lit}`path` when the operand gives a
value instead of a truth value. -/
def condition (path : List Nat) : Except ValueIssue Operand → Except ValueIssue Resolved.Expr
  | .ok (expression, _) =>
    if expression.isCondition then .ok expression
    else .error (.restriction path "a value used as a condition is not modeled; write a comparison")
  | .error issue => .error (issue.under path)

/-- Resolve an expression over the columns of the source table. An identifier is the
first column with its folded name; otherwise it is a string literal when it was
written in double quotes and {lit}`dqs` is on, else SQLite's
{lit}`no such column: %s`. The operands of {lit}`AND`, {lit}`OR` and {lit}`NOT` must be
conditions. An aggregate gives {name}`aggregateIssue`. -/
def resolveOperand (dqs : Bool) (columns : List CatalogColumn) (misuse : Bool) : Syntax.Expr → Except ValueIssue Operand
  | .identifier name doubleQuoted => match columnPosition columns name with
    | some position => .ok (.column position, (columns[position]?.map CatalogColumn.affinity))
    | none =>
      if doubleQuoted && dqs then .ok (.literal (.text name.toUTF8.toList), none)
      else .error (.prepare (.noSuchColumn name))
  | .equals left right => do
    let a ← (resolveOperand dqs columns misuse left).mapError (·.under [0])
    let b ← (resolveOperand dqs columns misuse right).mapError (·.under [1])
    match affinityIssue a b with
    | some (path, reason) => .error (.restriction path reason)
    | none => .ok (.compare .eq a.1 b.1, none)
  | .compare operator left right => do
    let a ← (resolveOperand dqs columns misuse left).mapError (·.under [1])
    let b ← (resolveOperand dqs columns misuse right).mapError (·.under [2])
    match affinityIssue a b with
    | some (path, reason) => .error (.restriction (path.map (· + 1)) reason)
    | none => .ok (.compare operator a.1 b.1, none)
  | .and left right => do
    let a ← condition [0] (resolveOperand dqs columns misuse left)
    let b ← condition [1] (resolveOperand dqs columns misuse right)
    .ok (.and a b, none)
  | .or left right => do
    let a ← condition [0] (resolveOperand dqs columns misuse left)
    let b ← condition [1] (resolveOperand dqs columns misuse right)
    .ok (.or a b, none)
  | .not operand => do
    let a ← condition [0] (resolveOperand dqs columns misuse operand)
    .ok (.not a, none)
  | .isNull operand negated => do
    let a ← (resolveOperand dqs columns misuse operand).mapError (·.under [0])
    .ok (.isNull a.1 negated, none)
  | call@(.callStar name) | call@(.call name _) =>
    .error (if aggregateCall call then aggregateIssue misuse name else unmodeledFunction)
  | literal@.null | literal@(.numeric _) | literal@(.string _) | literal@(.blob _)
  | literal@(.currentTime _) | literal@(.negate _) | literal@(.positive _) =>
    (literalValue dqs literal).map fun value => (.literal value, none)

end Belay.Sqlite
