import Belay.Sqlite.Model.Shared.Execution.SqlExecution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The reason of a statement that reads the clock in a run without a clock. -/
def clockUnmodeled : String :=
  "the statement reads the clock, which this run does not describe; write the time as a literal value"

/-- The reason of a statement that calls a counter function that the connection does not know
(ADR 0024, D2): it names the function and says how to make the value known. -/
def counterUnknownReason (kind : CounterKind) : String :=
  let function := match kind with
    | .changes => "changes()"
    | .totalChanges => "total_changes()"
    | .lastInsertRowid => "last_insert_rowid()"
  s!"the statement calls {function}, whose value on this connection the run does not know; start the run on a new connection"

end Belay.Sqlite.Model
