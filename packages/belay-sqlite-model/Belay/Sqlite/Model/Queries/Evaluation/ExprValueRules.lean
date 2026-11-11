import Belay.Sqlite.Model.Queries.Evaluation.ExprEvalLaws

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- The value of an arithmetic operator is the operator applied to the values of its operands
({name}`ArithmeticOperator.apply`). Proof sketch: the definition computes. -/
theorem Expr.eval_arithmetic (context : EvalContext) (row : List Value) (operator : ArithmeticOperator)
    (left right : Expr) :
    (Expr.arithmetic operator left right).eval context row =
      operator.apply (left.eval context row) (right.eval context row) := rfl

/-- The value of {lit}`CAST` is the conversion of the operand's value to the affinity
({name}`castValue`). Proof sketch: the definition computes. -/
theorem Expr.eval_cast (context : EvalContext) (row : List Value) (affinity : Affinity) (operand : Expr) :
    (Expr.cast affinity operand).eval context row = castValue affinity (operand.eval context row) := rfl

/-- The value of {lit}`COALESCE` is the first operand's value when it is not NULL, else the second's.
Proof sketch: the definition computes. -/
theorem Expr.eval_coalesce (context : EvalContext) (row : List Value) (first rest : Expr) :
    (Expr.coalesce first rest).eval context row =
      if (first.eval context row).isNull then rest.eval context row else first.eval context row := rfl

/-- The value of a JSON function call is the result of the function over the values of its
arguments and their JSON subtypes ({name}`Json.apply`), or NULL when it fails. Proof sketch: the
definition computes. -/
theorem Expr.eval_json (context : EvalContext) (row : List Value) (function : JsonFunction) (arguments : Arguments) :
    (Expr.json function arguments).eval context row =
      match Json.apply function ((arguments.eval context row).zip (arguments.givesJson context row)) with
      | .ok value => value
      | .error _ => .null := rfl

/-- The value of a date and time function call is its value at the context's clock over the
values of its arguments ({name}`DateFunction.value`). Proof sketch: the definition computes. -/
theorem Expr.eval_date (context : EvalContext) (row : List Value) (function : DateFunction) (arguments : Arguments) :
    (Expr.date function arguments).eval context row = function.value context.clock (arguments.eval context row) := rfl

/-- The value of an aggregate inside an expression is the context's value of the aggregate, or
NULL when the context has none at the index. Proof sketch: the definition computes. -/
theorem Expr.eval_aggregateValue (context : EvalContext) (row : List Value) (index : Nat) :
    (Expr.aggregateValue index).eval context row = context.aggregates.getD index .null := rfl

/-- The value of {lit}`x [NOT] IN (values)` is the membership test ({name}`inValue`) of the
operand's value among the values of the list. Proof sketch: the definition computes. -/
theorem Expr.eval_inList (context : EvalContext) (row : List Value) (operand : Expr) (values : Arguments)
    (affinity : Option Affinity) (collation : Collation) (negated : Bool) :
    (Expr.inList operand values affinity collation negated).eval context row =
      inValue affinity collation negated (operand.eval context row) (values.eval context row) := rfl

/-- The values of no arguments are no values. Proof sketch: the definition computes. -/
theorem Arguments.eval_nil (context : EvalContext) (row : List Value) : Arguments.nil.eval context row = [] := rfl

/-- The values of arguments are the value of the first argument, then the values of the rest, in written
order. Proof sketch: the definition computes. -/
theorem Arguments.eval_cons (context : EvalContext) (row : List Value) (head : Expr) (tail : Arguments) :
    (Arguments.cons head tail).eval context row = head.eval context row :: tail.eval context row := rfl

/-- The value of {lit}`iif` with its arguments is {name}`iifValue` of their values, and NULL
without arguments. Proof sketch: cases on the arguments; the definition computes. -/
theorem Expr.eval_iif (context : EvalContext) (row : List Value) (arguments : Arguments) :
    (Expr.scalar .iif arguments).eval context row =
      match arguments with
      | .nil => .null
      | .cons _ _ => iifValue (arguments.eval context row) := by
  cases arguments <;> rfl

/-- The value of a call of a scalar function other than {lit}`iif` is the function applied to
the values of its arguments ({name}`ScalarFunction.apply`), or NULL when it fails. Proof sketch:
cases on the function; the definition computes for each. -/
theorem Expr.eval_scalar (context : EvalContext) (row : List Value) {function : ScalarFunction}
    (notIif : function ≠ .iif) (arguments : Arguments) :
    (Expr.scalar function arguments).eval context row =
      match function.apply (arguments.eval context row) with
      | .ok value => value
      | .error _ => .null := by
  cases function <;> first | exact absurd rfl notIif | rfl

/-- {lit}`IS NULL` is true on a row exactly when its operand is NULL there, and {lit}`IS NOT NULL`
exactly when it is not. Proof sketch: the value is {name}`truth` of the test. -/
theorem truthy_isNull (context : EvalContext) (row : List Value) (operand : Expr) (negated : Bool) :
    truthy ((Expr.isNull operand negated).eval context row) = ((operand.eval context row).isNull != negated) := by
  rw [Expr.eval_isNull, truthy_truth]

end Belay.Sqlite.Model.Resolved
