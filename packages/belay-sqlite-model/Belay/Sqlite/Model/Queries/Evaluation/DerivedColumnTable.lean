import Belay.Sqlite.Model.Queries.Preparation.CatalogAddColumnSearch
import Belay.Sqlite.Model.Queries.Preparation.CatalogTriggerSearch
import Belay.Sqlite.Model.Queries.Evaluation.ExprEval

set_option doc.verso true

namespace Belay.Sqlite.Model
open Resolved

/-- Whether the value of an expression does not depend on the context in which it is evaluated: the clock,
the parameters, the counters and the subqueries. For example, {lit}`lower(a)` is context-free, and
{lit}`a + ?1` is not. A stored expression must be context-free, because the backfill evaluates it in the
context of one statement and a lookup evaluates it in the context of another. -/
def Resolved.Expr.ContextFree (expression : Resolved.Expr) : Prop :=
  ∀ (first second : EvalContext) (cells : List Value), expression.eval first cells = expression.eval second cells

end Belay.Sqlite.Model
