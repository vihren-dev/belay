import Belay.Sqlite.Model.Resolution.Resolve
import Belay.Sqlite.Model.SqlExecution

set_option doc.verso true

/-! The connection that a run of statements goes on from (ADR 0017, D3, amended 2026-10-22): the
state of the database with its transaction and counters, and the settings of
{lit}`PRAGMA foreign_keys` and {lit}`PRAGMA recursive_triggers`. {lit}`ScriptRun.lean` runs statements on
it. -/

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

/-- The connection after a statement that stopped with the outcome: an open transaction stays
open with its snapshot, as in SQLite; a failure outside a transaction, also after the rollback
of {lit}`OR ROLLBACK` ({name}`SqlState.failed`), leaves the connection idle. The database is
the outcome's, and the settings are those of the resolution state {lit}`after` the statement, and the counters are
those after the {lit}`counts` of the statement, which a failed write also gives (ADR 0024, D2). -/
def Connection.afterError (connection : Connection) (after : ResolveState) (counts : Counts) : Outcome → Connection
  | .success database | .failure _ _ database =>
    { state := { connection.state with
                 database := database, snapshot := none, counters := connection.state.counters.apply counts },
      foreignKeys := after.foreignKeys, recursiveTriggers := after.recursiveTriggers }
  | .pending persisted visible _ =>
    { state := { connection.state with
                 database := visible, snapshot := some persisted, counters := connection.state.counters.apply counts },
      foreignKeys := after.foreignKeys, recursiveTriggers := after.recursiveTriggers }

/-- The connection after a statement's transition: the state of a transition that continues,
with the settings of the resolution state {lit}`after` the statement, or
{name}`Connection.afterError` of a halt with the counts of the statement. -/
def Connection.afterStep (connection : Connection) (after : ResolveState) (counts : Counts) : SqlTransition → Connection
  | .next state => { state, foreignKeys := after.foreignKeys, recursiveTriggers := after.recursiveTriggers }
  | .halt outcome => connection.afterError after counts outcome

end Belay.Sqlite.Model
