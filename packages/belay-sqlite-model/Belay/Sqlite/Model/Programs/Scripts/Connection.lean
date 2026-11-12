import Belay.Sqlite.Model.Programs.Clock.SqlExecution
import Belay.Sqlite.Model.Schema.Dispatch.Connection

set_option doc.verso true

/-! The connection that a run of statements goes on from (ADR 0017, D3, amended 2026-10-22): the
state of the database with its transaction and counters, and the settings of
{lit}`PRAGMA foreign_keys` and {lit}`PRAGMA recursive_triggers`. {lit}`ScriptRun.lean` runs statements on
it. -/

namespace Belay.Sqlite.Model

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

/-- The connection after a statement that changes the stored database and the counters and nothing else:
the connection with the database, and with the counters after the counts of the statement. The snapshot of
an open transaction, the clock assignment and the settings stay. A successful plain write and a failed
write both give this connection. -/
def Connection.afterWrite (connection : Connection) (database : Database) (counts : Counts) : Connection :=
  { connection with state := { connection.state with
      database, counters := connection.state.counters.apply counts } }

/-- For every connection, database and counts: when the database has the catalog of the database of
the connection, the connection after the write ({name}`Connection.afterWrite`) has the
resolution state of the connection. So a write that changes rows and counters keeps the state in
which the next statements resolve. For example, {lean}`Database.setRows` keeps the catalog. Proof
sketch: the write changes neither the catalog, nor the snapshot, nor the settings. -/
theorem Connection.resolveState_afterWrite (connection : Connection) {database : Database}
    (counts : Counts) (catalog : database.catalog = connection.state.database.catalog) :
    (connection.afterWrite database counts).resolveState = connection.resolveState := by
  simp [Connection.resolveState, Connection.afterWrite, catalog]

end Belay.Sqlite.Model
