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
  | expression@(.compare _ _ left right) | expression@(.and left right) | expression@(.or left right)
  | expression@(.arithmetic _ left right) | expression@(.coalesce left right) =>
    test expression || left.any test || right.any test
  | expression@(.not operand) | expression@(.isNull operand _) | expression@(.cast _ operand) =>
    test expression || operand.any test
  | expression@(.json _ arguments) | expression@(.date _ arguments _) => test expression || arguments.any test

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
  | .cast .. | .coalesce .. | .now _ | .date .. => false

end Belay.Sqlite.Resolved
