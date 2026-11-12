import Belay.Sqlite.Model.Queries.Evaluation.QueryForm
import Belay.Sqlite.Model.Shared.Catalog.ExprAny

set_option doc.verso true

/-! A generic traversal of resolved expressions (ADR 0013, D7): whether a test holds for
the expression or one of its parts. Classification rules, such as "has a JSON call",
are a test over one node and this traversal, instead of a hand-written recursion each. -/

namespace Belay.Sqlite.Model.Resolved

/-- Whether the expression itself is a JSON call; its parts are not inspected. Use it with
{name}`Expr.any` to find a JSON call at any depth. -/
def Expr.isJsonCall : Expr → Bool
  | .json .. => true
  | .column _ | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .cast .. | .coalesce .. | .now _ | .date .. | .scalar .. | .exists .. | .inQuery .. | .subquery _ | .inList .. | .aggregateValue _ | .parameter _ | .counter _ => false

/-- Whether the expression itself is a call that can fail or give a value that the model
does not describe: a JSON call, or a scalar function that {name}`ScalarFunction.canFail`; its
parts are not inspected. Use it with {name}`Expr.any`. -/
def Expr.isFallibleCall : Expr → Bool
  | .json .. => true
  | .scalar function _ => function.canFail
  | .column _ | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .cast .. | .coalesce .. | .now _ | .date .. | .exists .. | .inQuery .. | .subquery _ | .inList .. | .aggregateValue _ | .parameter _ | .counter _ => false

/-- Whether the expression itself names a subquery of the statement: {lit}`EXISTS`, {lit}`IN`
of a subquery or a scalar subquery; its parts are not inspected. Use it with {name}`Expr.any`. -/
def Expr.namesSubquery : Expr → Bool
  | .exists _ | .inQuery .. | .subquery _ => true
  | .column _ | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .cast .. | .coalesce .. | .json .. | .now _ | .date .. | .scalar .. | .inList .. | .aggregateValue _ | .parameter _ | .counter _ => false

/-- Whether the expression itself is a date and time function call; its parts are not
inspected. -/
def Expr.isDateCall : Expr → Bool
  | .date .. => true
  | .column _ | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .cast .. | .coalesce .. | .json .. | .now _ | .scalar .. | .exists .. | .inQuery .. | .subquery _ | .inList .. | .aggregateValue _ | .parameter _ | .counter _ => false

/-- Whether the expression itself is {lit}`CURRENT_TIME`, {lit}`CURRENT_DATE` or
{lit}`CURRENT_TIMESTAMP`; its parts are not inspected. -/
def Expr.isNow : Expr → Bool
  | .now _ => true
  | .column _ | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .cast .. | .coalesce .. | .json .. | .date .. | .scalar .. | .exists .. | .inQuery .. | .subquery _ | .inList .. | .aggregateValue _ | .parameter _ | .counter _ => false

/-- Whether the expression itself is a call of {lit}`changes()`, {lit}`total_changes()` or
{lit}`last_insert_rowid()`; its parts are not inspected. Use it with {name}`Expr.any` to find a
read of a connection counter at any depth. -/
def Expr.isCounter : Expr → Bool
  | .counter _ => true
  | .column _ | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .cast .. | .coalesce .. | .json .. | .now _ | .date .. | .scalar .. | .exists .. | .inQuery .. | .subquery _ | .inList .. | .aggregateValue _ | .parameter _ => false

/-- Whether the expression itself is a parameter or a call of a counter function; its parts are
not inspected. -/
def Expr.isRunValue : Expr → Bool
  | .parameter _ | .counter _ => true
  | .column _ | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic .. | .cast ..
  | .coalesce .. | .json .. | .now _ | .date .. | .scalar .. | .exists .. | .inQuery .. | .subquery _ | .inList ..
  | .aggregateValue _ => false

/-- Whether the expression reads a parameter (ADR 0019, D1) or a counter (ADR 0024, D2)
anywhere: its value is known only when the statement runs, so resolution does not compute it. -/
def Expr.readsRunValue (expression : Expr) : Bool := expression.any Expr.isRunValue

end Belay.Sqlite.Model.Resolved
