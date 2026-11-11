import Belay.Sqlite.Model.Schema.Writes.StatementClock
import Belay.Sqlite.Model.Shared.Execution.StatementCounterReads

set_option doc.verso true

/-! The counters that a resolved statement reads (ADR 0024, D2): which of
{lit}`changes()`, {lit}`total_changes()` and {lit}`last_insert_rowid()` an expression of the
statement calls. The script run gives the statement the counters of the connection that it
reads and no others, so that a counter that the statement does not read cannot change its run. -/

namespace Belay.Sqlite.Model.Resolved

/-- The kinds of counter that a statement reads, without repeats, in the order of
{lit}`changes()`, {lit}`total_changes()`, {lit}`last_insert_rowid()`: the kinds that one of the
expressions of the statement, of its subqueries and of its trigger programs calls
({name}`Statement.clockExpressions`). For example, an INSERT whose trigger program selects
{lit}`changes()` reads the kind {lean}`CounterKind.changes` only. -/
def Statement.counterReads (statement : Statement) : List CounterKind :=
  [CounterKind.changes, .totalChanges, .lastInsertRowid].filter fun kind =>
    statement.clockExpressions.any fun expression => expression.any (Expr.readsCounterHere kind)

end Belay.Sqlite.Model.Resolved
