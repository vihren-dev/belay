import Belay.Sqlite.Model
import Belay.Sqlite.Resolution.QueryForm
import Belay.Sqlite.Comparison
import Belay.Sqlite.Json.JsonApply
import Belay.Sqlite.Date.Functions

set_option doc.verso true

/-! The value of an expression over one row, with its fault (ADR 0013, D2). SQLite
evaluates an expression lazily and folds some of it away (checked on native SQLite
3.51.0): it short-circuits {lit}`AND`, {lit}`OR` and {lit}`COALESCE`, and folds
{lit}`X AND 0` to 0 without evaluating {lit}`X`. The model evaluates every part and
records whether a JSON function of the expression fails: {lit}`must` when SQLite certainly
reports it, {lit}`may` when SQLite may skip it or the model does not describe it, and
{lit}`none` when no call fails. -/

namespace Belay.Sqlite.Resolved

/-- Whether a JSON function of an expression fails over a row. Use
{lean}`Fault.none` for an expression without a failing call. -/
inductive Fault where
  /-- No JSON call fails. -/
  | none
  /-- A JSON call fails, but SQLite may skip it, or its error is one that the model does
  not describe. -/
  | may
  /-- A JSON call fails where SQLite certainly evaluates it, with an error that the
  model describes. -/
  | must
  deriving Repr, DecidableEq

/-- The fault of two parts that SQLite both evaluates: the stronger one,
{lean}`Fault.may.join Fault.must = Fault.must`. -/
def Fault.join : Fault → Fault → Fault
  | .none, other => other
  | .may, .must => .must
  | .may, .none | .may, .may => .may
  | .must, .none | .must, .may | .must, .must => .must

/-- The fault of a part that SQLite may skip: a certain failure becomes possible,
{lean}`Fault.must.soften = Fault.may`. -/
def Fault.soften : Fault → Fault
  | .must => .may
  | .none => .none
  | .may => .may

/-- The fault of one JSON function result: {lit}`must` for malformed JSON, a bad path or bad
{lit}`json_valid` flags, which the model describes; {lit}`may` for a JSONB argument, which it
does not; {lit}`none` for a value. -/
def Fault.ofJson : Except Json.JsonError Value → Fault
  | .error .malformed | .error (.badPath _) | .error .badFlags => .must
  | .error .blobArgument => .may
  | .ok _ => .none

/-- Whether a REAL is not zero, as a condition. -/
def realTruthy (bits : UInt64) : Bool := (realScaled bits).any (· != 0)

/-- Whether a value is true as a condition, as SQLite's {lit}`sqlite3VdbeBooleanValue` gives
it: an integer that is not zero, a REAL that is not zero, and TEXT or BLOB whose numeric
prefix ({name}`atof`) is not zero; NULL is not true. So {lit}`'1ab'` and {lit}`'0.9'` are
true and {lit}`'abc'` is not. -/
def truthy : Value → Bool
  | .integer value => value != 0
  | .real bits => realTruthy bits
  | .text bytes | .blob bytes => realTruthy (atof bytes).1.toBits
  | .null => false

/-- Whether a value is false as a condition: not NULL and not true. -/
def falsy (value : Value) : Bool := !value.isNull && !truthy value

/-- A comparison operand after a numeric affinity: TEXT that looks like a number becomes
that number ({name}`numericText`); every other value stays, so an integer never goes
through a double. -/
def numericOperand : Value → Value
  | .text bytes => numericText bytes
  | value@(.null) | value@(.integer _) | value@(.real _) | value@(.blob _) => value

/-- Whether a value is TEXT. -/
def _root_.Belay.Sqlite.Value.isText : Value → Bool
  | .text _ => true
  | .null | .integer _ | .real _ | .blob _ => false

/-- The operands of a comparison after SQLite applies its affinity (the comparison
opcodes of {lit}`sqlite3VdbeExec`): with INTEGER, REAL or NUMERIC, each TEXT operand that
looks like a number becomes that number ({name}`numericOperand`); with TEXT, when an operand
is TEXT, each number becomes its text ({name}`storeValue`), which the order would also give
otherwise; with BLOB or none, the operands stay. -/
def comparisonOperands : Option Affinity → Value → Value → Value × Value
  | some .integer, left, right | some .real, left, right | some .numeric, left, right =>
    (numericOperand left, numericOperand right)
  | some .text, left, right =>
    if left.isText || right.isText then (storeValue .text left, storeValue .text right) else (left, right)
  | some .blob, left, right | none, left, right => (left, right)

mutual
/-- The value of an expression over the cells of one row, in column order, with its
{name}`Fault`. A column past the end of the row reads as NULL. {lit}`AND` is false when an
operand is false, else NULL when an operand is NULL, else true; {lit}`OR` is the dual;
{lit}`NOT` keeps NULL; a comparison applies its affinity first
({name}`comparisonOperands`). Arithmetic and {lit}`CAST` follow {name}`ArithmeticOperator.apply`
and {name}`castValue`; {lit}`COALESCE` gives its first operand unless that is NULL. A JSON
function gives the value of {name}`Json.apply` over the values of its arguments, and NULL
with {name}`Fault.ofJson` when it fails. The fault of {lit}`AND`, {lit}`OR` and
{lit}`COALESCE` is softened ({name}`Fault.soften`), because SQLite may skip an operand; every
other expression joins the faults of its parts ({name}`Fault.join`). {lit}`clock` is the
statement's clock value in Julian-day milliseconds: a time keyword is its text at the clock
value ({lit}`TimeKeyword.value`), and a date and time function gives
{lit}`DateFunction.value` at the clock value. -/
def Expr.evaluate (clock : Int) (row : List Value) : Expr → Value × Fault
  | .column position => (row.getD position .null, .none)
  | .literal value => (value, .none)
  | .compare operator affinity left right =>
    let (a, first) := left.evaluate clock row
    let (b, second) := right.evaluate clock row
    let (a, b) := comparisonOperands affinity a b
    (operator.apply a b, first.join second)
  | .and left right =>
    let (a, first) := left.evaluate clock row
    let (b, second) := right.evaluate clock row
    (if falsy a || falsy b then truth false else if a.isNull || b.isNull then .null else truth true,
      (first.join second).soften)
  | .or left right =>
    let (a, first) := left.evaluate clock row
    let (b, second) := right.evaluate clock row
    (if truthy a || truthy b then truth true else if a.isNull || b.isNull then .null else truth false,
      (first.join second).soften)
  | .not operand =>
    let (value, fault) := operand.evaluate clock row
    (if value.isNull then .null else truth (!truthy value), fault)
  | .isNull operand negated =>
    let (value, fault) := operand.evaluate clock row
    (truth (value.isNull != negated), fault)
  | .arithmetic operator left right =>
    let (a, first) := left.evaluate clock row
    let (b, second) := right.evaluate clock row
    (operator.apply a b, first.join second)
  | .cast affinity operand =>
    let (value, fault) := operand.evaluate clock row
    (castValue affinity value, fault)
  | .coalesce first rest =>
    let (value, fault) := first.evaluate clock row
    let (other, later) := rest.evaluate clock row
    (if value.isNull then other else value, (fault.join later).soften)
  | .json function arguments =>
    let (values, fault) := arguments.evaluate clock row
    let result := Json.apply function values
    (match result with
      | .ok value => value
      | .error _ => .null, fault.join (Fault.ofJson result))
  | .date function arguments =>
    let (values, fault) := arguments.evaluate clock row
    (function.value clock values, fault)
  | .now keyword => (keyword.value clock, .none)

/-- The values of the arguments of a call over one row, in written order, with the
joined fault of the arguments. -/
def Arguments.evaluate (clock : Int) (row : List Value) : Arguments → List Value × Fault
  | .nil => ([], .none)
  | .cons head tail =>
    let (value, fault) := head.evaluate clock row
    let (values, later) := tail.evaluate clock row
    (value :: values, fault.join later)
end

/-- The value of an expression over one row at a clock value: the value of
{name}`Expr.evaluate`. -/
def Expr.eval (clock : Int) (row : List Value) (expression : Expr) : Value := (expression.evaluate clock row).1

/-- The values of the arguments of a call over one row at a clock value: the values of
{name}`Arguments.evaluate`. -/
def Arguments.eval (clock : Int) (row : List Value) (arguments : Arguments) : List Value :=
  (arguments.evaluate clock row).1

/-- Whether the fault of the expression over the row at the clock value is not
{lean}`Fault.none`. -/
def Expr.mayFailOn (clock : Int) (row : List Value) (expression : Expr) : Bool :=
  (expression.evaluate clock row).2 != .none

/-- Whether the fault of the expression over the row at the clock value is
{lean}`Fault.must`. -/
def Expr.mustFailOn (clock : Int) (row : List Value) (expression : Expr) : Bool :=
  (expression.evaluate clock row).2 == .must

end Belay.Sqlite.Resolved
