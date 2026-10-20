import Belay.Sqlite.Model
import Belay.Sqlite.Resolution.QueryForm
import Belay.Sqlite.Comparison
import Belay.Sqlite.Json.JsonApply
import Belay.Sqlite.Functions.Scalar

set_option doc.verso true

/-! The parts of expression evaluation that are not recursive (ADR 0013, D2): the
{lit}`Fault` of a part and how faults combine, the fault of a JSON or scalar function
result, SQLite's truth test of a value, and the operands of a comparison after its affinity. -/

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

/-- The fault of one JSON function result: {lit}`must` for malformed JSON, a bad path, bad
{lit}`json_valid` flags and the argument errors of {lit}`json_object` and the edit functions,
which the model describes; {lit}`may` for a JSONB argument and for the error position of
malformed JSON, which it does not; {lit}`none` for a value. -/
def Fault.ofJson : Except Json.JsonError Value → Fault
  | .error .malformed | .error (.badPath _) | .error .badFlags | .error .objectArgumentCount
  | .error .labelNotText | .error (.editArgumentCount _) | .error .blobValue => .must
  | .error .blobArgument | .error .unmodeledPosition => .may
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

/-- The fault of a scalar function result: {lit}`must` for a failure that SQLite reports,
{lit}`may` for a value that the model does not describe, {lit}`none` for a value. -/
def Fault.ofFunction : Except FunctionFailure Value → Fault
  | .error .error => .must
  | .error .unmodeled => .may
  | .ok _ => .none

/-- The value of {lit}`iif` over its argument values, as SQLite's {lit}`CASE` code computes it:
the value after the first condition that is true ({name}`truthy`), else the last value of an
odd number of arguments, else NULL. For example, {lean}`iifValue [.integer 0, .integer 1, .integer 2] = .integer 2`. -/
def iifValue : List Value → Value
  | [] => .null
  | [value] => value
  | condition :: value :: rest => if truthy condition then value else iifValue rest

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

end Belay.Sqlite.Resolved
