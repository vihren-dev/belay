import Belay.Sqlite.ExprFault
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

mutual
/-- The value of an expression over the cells of one row, in column order, with its
{name}`Fault`. A column past the end of the row reads as NULL. {lit}`AND` is false when an
operand is false, else NULL when an operand is NULL, else true; {lit}`OR` is the dual;
{lit}`NOT` keeps NULL; a comparison applies its affinity first
({name}`comparisonOperands`). Arithmetic and {lit}`CAST` follow {name}`ArithmeticOperator.apply`
and {name}`castValue`; {lit}`COALESCE` gives its first operand unless that is NULL. A JSON
function gives the value of {name}`Json.apply` over the values of its arguments, each with
whether it has the JSON subtype ({lit}`Arguments.givesJson`), and NULL with
{name}`Fault.ofJson` when it fails. The fault of {lit}`AND`, {lit}`OR` and
{lit}`COALESCE` is softened ({name}`Fault.soften`), because SQLite may skip an operand; every
other expression joins the faults of its parts ({name}`Fault.join`). {lit}`clock` is the
statement's clock value in Julian-day milliseconds: a time keyword is its text at the clock
value ({lit}`TimeKeyword.value`), and a date and time function gives
{lit}`DateFunction.value` at the clock value. A scalar function of ADR 0015 gives
{name}`ScalarFunction.apply` over its argument values, and NULL with {name}`Fault.ofFunction`
when it fails; {lit}`iif` gives {name}`iifValue`, and only its first argument is certain
to run, so the faults of the others are softened. -/
def Expr.evaluate (clock : Int) (row : List Value) : Expr → Value × Fault
  | .column position => (row.getD position .null, .none)
  | .literal value => (value, .none)
  | .compare operator affinity left right collation =>
    let (a, first) := left.evaluate clock row
    let (b, second) := right.evaluate clock row
    let (a, b) := comparisonOperands affinity a b
    (operator.apply a b collation, first.join second)
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
    let result := Json.apply function (values.zip (arguments.givesJson clock row))
    (match result with
      | .ok value => value
      | .error _ => .null, fault.join (Fault.ofJson result))
  | .date function arguments =>
    let (values, fault) := arguments.evaluate clock row
    (function.value clock values, fault)
  | .now keyword => (keyword.value clock, .none)
  | .scalar .iif .nil => (.null, .none)
  | .scalar .iif (.cons condition rest) =>
    let (value, fault) := condition.evaluate clock row
    let (values, later) := rest.evaluate clock row
    (iifValue (value :: values), fault.join later.soften)
  | .scalar function arguments =>
    let (values, fault) := arguments.evaluate clock row
    let result := function.apply values
    (match result with
      | .ok value => value
      | .error _ => .null, fault.join (Fault.ofFunction result))

/-- The values of the arguments of a call over one row, in written order, with the
joined fault of the arguments. -/
def Arguments.evaluate (clock : Int) (row : List Value) : Arguments → List Value × Fault
  | .nil => ([], .none)
  | .cons head tail =>
    let (value, fault) := head.evaluate clock row
    let (values, later) := tail.evaluate clock row
    (value :: values, fault.join later)

/-- Whether the value of an expression over one row has SQLite's JSON subtype, which makes a
JSON function read a text argument as JSON: a call of a function that always gives it
({name}`JsonFunction.givesJson`), {lit}`json_extract` with two or more paths, and with one path
when it selects an array or an object ({name}`Json.extractGivesJson`). Any other expression
gives false; resolution refuses an argument whose subtype the model does not describe
(restriction {lit}`json-subtype`). -/
def Expr.givesJson (clock : Int) (row : List Value) : Expr → Bool
  | .json .extract (.cons json (.cons path .nil)) =>
    Json.extractGivesJson (json.evaluate clock row).1 (path.evaluate clock row).1
  | .json .extract (.cons _ (.cons _ (.cons _ _))) => true
  | .json function _ => function.givesJson
  | .column _ | .literal _ | .compare _ _ _ _ _ | .and _ _ | .or _ _ | .not _ | .isNull _ _
  | .arithmetic _ _ _ | .cast _ _ | .coalesce _ _ | .now _ | .date _ _ | .scalar _ _ => false

/-- Whether each argument of a call over one row has SQLite's JSON subtype
({lit}`Expr.givesJson`), in written order. -/
def Arguments.givesJson (clock : Int) (row : List Value) : Arguments → List Bool
  | .nil => []
  | .cons head tail => head.givesJson clock row :: tail.givesJson clock row
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
