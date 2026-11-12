import Belay.Sqlite.Model.Schema.Dispatch.Resolve
import Belay.Sqlite.Model.Shared.Execution.SqlExecution
import Belay.Sqlite.Model.Schema.Dispatch.SqlAdvance

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The state of a connection between two statements: the visible database, the snapshot of
an open transaction, a clock assignment and the counters ({name}`SqlState`), and the settings of
{lit}`PRAGMA foreign_keys` and {lit}`PRAGMA recursive_triggers`. For example,
{lean}`({ state := { database := {} } } : Connection)` is an idle connection to the empty
database with both settings off. The run of this file takes
its clock as an argument and does not read the clock assignment of the state; the laws of
{lit}`ScriptRunLaws.lean` compare the run with {name}`runSqlFrom` on the state, which reads it. -/
structure Connection where
  /-- The database, the open transaction, the clock assignment (which the run carries without
  a change) and the counters (which each statement that writes changes). -/
  state : SqlState
  /-- Whether foreign keys are on; off by default, as in SQLite. -/
  foreignKeys : Bool := false
  /-- Whether recursive triggers are on; off by default, as in SQLite. -/
  recursiveTriggers : Bool := false

/-- The state of resolution for the next statement: the catalog of the visible database, the
catalog of the snapshot of an open transaction, and the settings. -/
def Connection.resolveState (connection : Connection) : ResolveState :=
  { catalog := connection.state.database.catalog, saved := connection.state.snapshot.map (·.catalog),
    foreignKeys := connection.foreignKeys, recursiveTriggers := connection.recursiveTriggers }

end Belay.Sqlite.Model
