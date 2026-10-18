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

/-- Whether a value is true as a condition: a number that is not zero. -/
def truthy : Value → Bool
  | .integer value => value != 0
  | .real bits => (realScaled bits).any (· != 0)
  | .null | .text _ | .blob _ => false

/-- Whether a value is false as a condition: not NULL and not true. -/
def falsy (value : Value) : Bool := !value.isNull && !truthy value

mutual
/-- The value of an expression over the cells of one row, in column order, with its
{name}`Fault`. A column past the end of the row reads as NULL. {lit}`AND` is false when an
operand is false, else NULL when an operand is NULL, else true; {lit}`OR` is the dual;
{lit}`NOT` keeps NULL. Arithmetic and {lit}`CAST` follow {name}`ArithmeticOperator.apply`
and {name}`castValue`; {lit}`COALESCE` gives its first operand unless that is NULL. A JSON
function gives the value of {name}`Json.apply` over the values of its arguments, and NULL
with {name}`Fault.ofJson` when it fails. The fault of {lit}`AND`, {lit}`OR` and
{lit}`COALESCE` is softened ({name}`Fault.soften`), because SQLite may skip an operand; every
other expression joins the faults of its parts ({name}`Fault.join`). A time keyword is NULL
here: the execution replaces it with the statement's clock text first
({lit}`Statement.atClock`). A date and time function gives the value of
{lit}`DateFunction.value` at its stored clock value. -/
def Expr.evaluate (row : List Value) : Expr → Value × Fault
  | .column position => (row.getD position .null, .none)
  | .literal value => (value, .none)
  | .compare operator left right =>
    let (a, first) := left.evaluate row
    let (b, second) := right.evaluate row
    (operator.apply a b, first.join second)
  | .and left right =>
    let (a, first) := left.evaluate row
    let (b, second) := right.evaluate row
    (if falsy a || falsy b then truth false else if a.isNull || b.isNull then .null else truth true,
      (first.join second).soften)
  | .or left right =>
    let (a, first) := left.evaluate row
    let (b, second) := right.evaluate row
    (if truthy a || truthy b then truth true else if a.isNull || b.isNull then .null else truth false,
      (first.join second).soften)
  | .not operand =>
    let (value, fault) := operand.evaluate row
    (if value.isNull then .null else truth (!truthy value), fault)
  | .isNull operand negated =>
    let (value, fault) := operand.evaluate row
    (truth (value.isNull != negated), fault)
  | .arithmetic operator left right =>
    let (a, first) := left.evaluate row
    let (b, second) := right.evaluate row
    (operator.apply a b, first.join second)
  | .cast affinity operand =>
    let (value, fault) := operand.evaluate row
    (castValue affinity value, fault)
  | .coalesce first rest =>
    let (value, fault) := first.evaluate row
    let (other, later) := rest.evaluate row
    (if value.isNullCell then other else value, (fault.join later).soften)
  | .json function arguments =>
    let (values, fault) := arguments.evaluate row
    let result := Json.apply function values
    (match result with
      | .ok value => value
      | .error _ => .null, fault.join (Fault.ofJson result))
  | .date function arguments clock =>
    let (values, fault) := arguments.evaluate row
    (function.value clock values, fault)
  | .now _ => (.null, .none)

/-- The values of the arguments of a call over one row, in written order, with the
joined fault of the arguments. -/
def Arguments.evaluate (row : List Value) : Arguments → List Value × Fault
  | .nil => ([], .none)
  | .cons head tail =>
    let (value, fault) := head.evaluate row
    let (values, later) := tail.evaluate row
    (value :: values, fault.join later)
end

/-- The value of an expression over one row: the value of {name}`Expr.evaluate`. -/
def Expr.eval (row : List Value) (expression : Expr) : Value := (expression.evaluate row).1

/-- The values of the arguments of a call over one row: the values of
{name}`Arguments.evaluate`. -/
def Arguments.eval (row : List Value) (arguments : Arguments) : List Value := (arguments.evaluate row).1

/-- Whether the fault of the expression over the row is not {lean}`Fault.none`. -/
def Expr.mayFailOn (row : List Value) (expression : Expr) : Bool := (expression.evaluate row).2 != .none

/-- Whether the fault of the expression over the row is {lean}`Fault.must`. -/
def Expr.mustFailOn (row : List Value) (expression : Expr) : Bool := (expression.evaluate row).2 == .must

end Belay.Sqlite.Resolved
