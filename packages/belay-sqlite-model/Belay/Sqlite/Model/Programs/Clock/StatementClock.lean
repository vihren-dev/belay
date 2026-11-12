import Belay.Sqlite.Model.Schema.Writes.JsonReady
import Belay.Sqlite.Model.Queries.Evaluation.StatementClock

set_option doc.verso true

/-! The clock of a resolved statement (ADR 0012, amendment 5, slice 6e2; ADR 0013, D6): the
cells of INSERT rows in the statement's evaluation context, whose clock value is the
statement's, and whether a statement reads the clock at all. Evaluation takes the context
as a parameter, so a statement is never rewritten for a clock value. -/

namespace Belay.Sqlite.Model.Resolved

/-- Whether a statement reads the clock: it has an expression that reads it
({name}`Expr.readsClock`, {name}`Statement.clockExpressions`). The execution gives a
statement that does not the clock value 0, which it does not read ({lit}`runSqlAt`). -/
def Statement.readsClock (statement : Statement) : Bool :=
  statement.clockExpressions.any Expr.readsClock

end Belay.Sqlite.Model.Resolved
