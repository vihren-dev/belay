import Belay.Sqlite.Model.Schema.Dispatch.Connection
import Belay.Sqlite.Model.Schema.Writes.PlainWriteFrame

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- What a plain write to another table, or a read, cannot change at a position: the catalog, the table
at the position with its rows, the snapshot of an open transaction, and the two connection settings. The
counters are not in it, because every write and some reads change them. -/
def Connection.shelter (position : Nat) (connection : Connection) :
    Catalog × Option Table × Option Model.Database × Bool × Bool :=
  (connection.state.database.catalog, connection.state.database.table position, connection.state.snapshot,
    connection.foreignKeys, connection.recursiveTriggers)

/-- For every position and two connections with the same shelter: both connections give the same state of
resolution. Proof sketch: the state of resolution is made of the catalog, the catalog of the snapshot and the
two settings, which the shelter holds. -/
theorem Connection.shelter_resolveState {position : Nat} {connection other : Connection}
    (same : connection.shelter position = other.shelter position) :
    connection.resolveState = other.resolveState := by
  simp only [Connection.shelter, Prod.mk.injEq] at same
  obtain ⟨catalog, -, snapshot, foreignKeys, recursiveTriggers⟩ := same
  simp [Connection.resolveState, catalog, snapshot, foreignKeys, recursiveTriggers]

/-- A resolved statement that leaves the shelter of a position unchanged: a plain write to a table other than
the table at the position, or a query, or a statement that SQLite refuses with a prepare error. For example,
an INSERT into another table is sheltered from position 0 when its table is not at position 0. -/
def Resolved.Statement.ShelteredFrom (position : Nat) (statement : Resolved.Statement) : Prop :=
  (∃ target, statement.plainWriteTarget = some target ∧ target ≠ position) ∨
    (∃ query subqueries, statement = .query query subqueries) ∨ ∃ error, statement = .prepareError error

end Belay.Sqlite.Model
