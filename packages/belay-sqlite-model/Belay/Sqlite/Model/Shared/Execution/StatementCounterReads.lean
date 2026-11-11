import Belay.Sqlite.Model.Shared.Catalog.ExprAny

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- Whether the expression itself is a call of the counter function of the kind; its parts are
not inspected. Use it with {name}`Expr.any`. -/
def Expr.readsCounterHere (kind : CounterKind) : Expr → Bool
  | .counter other => other = kind
  | .column _ | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic .. | .cast ..
  | .coalesce .. | .json .. | .now _ | .date .. | .scalar .. | .exists .. | .inQuery .. | .subquery _ | .inList ..
  | .aggregateValue _ | .parameter _ => false

end Belay.Sqlite.Model.Resolved
