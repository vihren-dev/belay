import Belay.Sqlite.Model.Queries.Evaluation.ExprValueRules

set_option doc.verso true

/-! The fault rules of the resolved expressions (ADR 0027 D1, expression phase): for each of the
21 constructors that {lit}`ExprEvalLaws.lean` does not cover, the fault of the expression on a row
({name}`Belay.Sqlite.Model.Resolved.Expr.evaluate`) in the faults of its parts. A column, a
literal, a parameter, a time keyword, a counter call and an aggregate value have no fault; a
comparison, arithmetic and {lit}`IN` of a list join the faults of their parts
({name}`Belay.Sqlite.Model.Resolved.Fault.join`), and {lit}`AND`, {lit}`OR`, {lit}`COALESCE`
soften them ({name}`Belay.Sqlite.Model.Resolved.Fault.soften`), because SQLite may skip an
operand; a function call adds the fault of its result. A value rule does not discharge the fault
obligation: the execution rule needs both. -/

namespace Belay.Sqlite.Model.Resolved

/-- A column has no fault. Proof sketch: the definition computes. -/
theorem Expr.fault_column (context : EvalContext) (row : List Value) (position : Nat) :
    ((Expr.column position).evaluate context row).2 = .none := rfl

/-- A literal has no fault. Proof sketch: the definition computes. -/
theorem Expr.fault_literal (context : EvalContext) (row : List Value) (value : Value) :
    ((Expr.literal value).evaluate context row).2 = .none := rfl

/-- A parameter has no fault. Proof sketch: the definition computes. -/
theorem Expr.fault_parameter (context : EvalContext) (row : List Value) (number : Nat) :
    ((Expr.parameter number).evaluate context row).2 = .none := rfl

/-- A time keyword has no fault. Proof sketch: the definition computes. -/
theorem Expr.fault_now (context : EvalContext) (row : List Value) (keyword : TimeKeyword) :
    ((Expr.now keyword).evaluate context row).2 = .none := rfl

/-- A counter call has no fault. Proof sketch: the definition computes. -/
theorem Expr.fault_counter (context : EvalContext) (row : List Value) (kind : CounterKind) :
    ((Expr.counter kind).evaluate context row).2 = .none := rfl

/-- An aggregate value has no fault. Proof sketch: the definition computes. -/
theorem Expr.fault_aggregateValue (context : EvalContext) (row : List Value) (index : Nat) :
    ((Expr.aggregateValue index).evaluate context row).2 = .none := rfl

/-- The fault of a comparison is the join of the faults of its operands. Proof sketch: the
definition computes. -/
theorem Expr.fault_compare (context : EvalContext) (row : List Value) (operator : Comparison)
    (affinity : Option Affinity) (left right : Expr) (collation : Collation) :
    ((Expr.compare operator affinity left right collation).evaluate context row).2 =
      (left.evaluate context row).2.join (right.evaluate context row).2 := rfl

/-- The fault of {lit}`AND` is the softened join of the faults of its operands. Proof sketch: the
definition computes. -/
theorem Expr.fault_and (context : EvalContext) (row : List Value) (left right : Expr) :
    ((Expr.and left right).evaluate context row).2 =
      ((left.evaluate context row).2.join (right.evaluate context row).2).soften := rfl

/-- The fault of {lit}`OR` is the softened join of the faults of its operands. Proof sketch: the
definition computes. -/
theorem Expr.fault_or (context : EvalContext) (row : List Value) (left right : Expr) :
    ((Expr.or left right).evaluate context row).2 =
      ((left.evaluate context row).2.join (right.evaluate context row).2).soften := rfl

/-- The fault of {lit}`IS NULL` is the fault of its operand. Proof sketch: the definition
computes. -/
theorem Expr.fault_isNull (context : EvalContext) (row : List Value) (operand : Expr) (negated : Bool) :
    ((Expr.isNull operand negated).evaluate context row).2 = (operand.evaluate context row).2 := rfl

/-- The fault of an arithmetic operator is the join of the faults of its operands. Proof sketch:
the definition computes. -/
theorem Expr.fault_arithmetic (context : EvalContext) (row : List Value) (operator : ArithmeticOperator)
    (left right : Expr) :
    ((Expr.arithmetic operator left right).evaluate context row).2 =
      (left.evaluate context row).2.join (right.evaluate context row).2 := rfl

/-- The fault of {lit}`CAST` is the fault of its operand. Proof sketch: the definition computes. -/
theorem Expr.fault_cast (context : EvalContext) (row : List Value) (affinity : Affinity) (operand : Expr) :
    ((Expr.cast affinity operand).evaluate context row).2 = (operand.evaluate context row).2 := rfl

/-- The fault of {lit}`COALESCE` is the softened join of the faults of its operands. Proof sketch:
the definition computes. -/
theorem Expr.fault_coalesce (context : EvalContext) (row : List Value) (first rest : Expr) :
    ((Expr.coalesce first rest).evaluate context row).2 =
      ((first.evaluate context row).2.join (rest.evaluate context row).2).soften := rfl

/-- The fault of a JSON function call is the fault of its arguments joined with the fault of
its result ({name}`Fault.ofJson`). Proof sketch: the definition computes. -/
theorem Expr.fault_json (context : EvalContext) (row : List Value) (function : JsonFunction) (arguments : Arguments) :
    ((Expr.json function arguments).evaluate context row).2 =
      (arguments.evaluate context row).2.join
        (Fault.ofJson (Json.apply function ((arguments.eval context row).zip (arguments.givesJson context row)))) := rfl

/-- The fault of a date and time function call is the fault of its arguments. Proof sketch: the
definition computes. -/
theorem Expr.fault_date (context : EvalContext) (row : List Value) (function : DateFunction) (arguments : Arguments) :
    ((Expr.date function arguments).evaluate context row).2 = (arguments.evaluate context row).2 := rfl

/-- The fault of {lit}`x [NOT] IN (values)` is the fault of the operand joined with the softened
fault of the values. Proof sketch: the definition computes. -/
theorem Expr.fault_inList (context : EvalContext) (row : List Value) (operand : Expr) (values : Arguments)
    (affinity : Option Affinity) (collation : Collation) (negated : Bool) :
    ((Expr.inList operand values affinity collation negated).evaluate context row).2 =
      (operand.evaluate context row).2.join (values.evaluate context row).2.soften := rfl

/-- The fault of {lit}`iif` is none without arguments, else the fault of its first argument
joined with the softened fault of the others. Proof sketch: cases on the arguments; the
definition computes. -/
theorem Expr.fault_iif (context : EvalContext) (row : List Value) (arguments : Arguments) :
    ((Expr.scalar .iif arguments).evaluate context row).2 =
      match arguments with
      | .nil => .none
      | .cons condition rest => (condition.evaluate context row).2.join (rest.evaluate context row).2.soften := by
  cases arguments <;> rfl

/-- The fault of a call of a scalar function other than {lit}`iif` is the fault of its arguments
joined with the fault of its result ({name}`Fault.ofFunction`). Proof sketch: cases on the
function; the definition computes for each. -/
theorem Expr.fault_scalar (context : EvalContext) (row : List Value) {function : ScalarFunction}
    (notIif : function ≠ .iif) (arguments : Arguments) :
    ((Expr.scalar function arguments).evaluate context row).2 =
      (arguments.evaluate context row).2.join (Fault.ofFunction (function.apply (arguments.eval context row))) := by
  cases function <;> first | exact absurd rfl notIif | rfl

end Belay.Sqlite.Model.Resolved
