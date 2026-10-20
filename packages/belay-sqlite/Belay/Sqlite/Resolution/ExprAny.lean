import Belay.Sqlite.Resolution.QueryForm

set_option doc.verso true

/-! A generic traversal of resolved expressions (ADR 0013, D7): whether a test holds for
the expression or one of its parts. Classification rules, such as "has a JSON call",
are a test over one node and this traversal, instead of a hand-written recursion each. -/

namespace Belay.Sqlite.Resolved

mutual
/-- Whether the test holds for the expression or for one of its subexpressions, at any
depth, including the arguments of calls. -/
def Expr.any (test : Expr → Bool) : Expr → Bool
  | expression@(.column _) | expression@(.literal _) | expression@(.now _) => test expression
  | expression@(.compare _ _ left right _) | expression@(.and left right) | expression@(.or left right)
  | expression@(.arithmetic _ left right) | expression@(.coalesce left right) =>
    test expression || left.any test || right.any test
  | expression@(.not operand) | expression@(.isNull operand _) | expression@(.cast _ operand) =>
    test expression || operand.any test
  | expression@(.json _ arguments) | expression@(.date _ arguments) | expression@(.scalar _ arguments) =>
    test expression || arguments.any test

/-- Whether the test holds for one of the arguments or their subexpressions
({name}`Expr.any`). -/
def Arguments.any (test : Expr → Bool) : Arguments → Bool
  | .nil => false
  | .cons head tail => head.any test || tail.any test
end

/-- Whether the expression itself is a JSON call; its parts are not inspected. Use it with
{name}`Expr.any` to find a JSON call at any depth. -/
def Expr.isJsonCall : Expr → Bool
  | .json .. => true
  | .column _ | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .cast .. | .coalesce .. | .now _ | .date .. | .scalar .. => false

/-- Whether the expression itself is a call that can fail or give a value that the model
does not describe: a JSON call, or a scalar function that {name}`ScalarFunction.canFail`; its
parts are not inspected. Use it with {name}`Expr.any`. -/
def Expr.isFallibleCall : Expr → Bool
  | .json .. => true
  | .scalar function _ => function.canFail
  | .column _ | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .cast .. | .coalesce .. | .now _ | .date .. => false

/-- Whether the expression itself is a date and time function call; its parts are not
inspected. -/
def Expr.isDateCall : Expr → Bool
  | .date .. => true
  | .column _ | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .cast .. | .coalesce .. | .json .. | .now _ | .scalar .. => false

/-- Whether the expression itself is {lit}`CURRENT_TIME`, {lit}`CURRENT_DATE` or
{lit}`CURRENT_TIMESTAMP`; its parts are not inspected. -/
def Expr.isNow : Expr → Bool
  | .now _ => true
  | .column _ | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .cast .. | .coalesce .. | .json .. | .date .. | .scalar .. => false

/-- Whether the expression itself is the column at the position; its parts are not
inspected. -/
def Expr.isColumn (position : Nat) : Expr → Bool
  | .column read => read == position
  | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic .. | .cast ..
  | .coalesce .. | .json .. | .now _ | .date .. | .scalar .. => false

/-- Whether the expression itself is a column at the position or after it; its parts are
not inspected. -/
def Expr.isColumnFrom (width : Nat) : Expr → Bool
  | .column read => read ≥ width
  | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic .. | .cast ..
  | .coalesce .. | .json .. | .now _ | .date .. | .scalar .. => false

/-- Whether the expression reads only columns below the width. -/
def Expr.readsBelow (width : Nat) (expression : Expr) : Bool := !expression.any (Expr.isColumnFrom width)

/-- Whether the expression reads the column at the position anywhere. -/
def Expr.readsColumn (position : Nat) (expression : Expr) : Bool := expression.any (Expr.isColumn position)

/-- The positions below the width that the expression reads, in increasing order. For
example the expression {lit}`a + c` over the columns {lit}`a, b, c` reads {lean}`[0, 2]`. -/
def Expr.reads (width : Nat) (expression : Expr) : List Nat :=
  (List.range width).filter expression.readsColumn

end Belay.Sqlite.Resolved
