import Belay.Sqlite.Model.SqlState

set_option doc.verso true

/-! Laws of the connection state ({lit}`SqlState.lean`): what {lit}`SqlState.failed` gives
for each error, and the error of an outcome. -/

namespace Belay.Sqlite.Model

/-- For every database, position, reason and result database, the failure of an idle
state is the plain failure. Proof sketch: without a snapshot both branches of the reason
test finish to the failure itself. -/
@[simp] theorem SqlState.failed_idle (current : Database) (position : Nat) (reason : ExecutionError)
    (database : Database) : ({ database := current } : SqlState).failed position reason database =
      .failure position reason database := by
  unfold SqlState.failed SqlState.finish
  split <;> rfl

/-- The error of an outcome: the reason of a failure, the error of a pending result, or
none. -/
def Outcome.error? : Outcome → Option ExecutionError
  | .success _ => none
  | .failure _ reason _ => some reason
  | .pending _ _ error => error.map (·.2)

/-- For every state, position, reason and database, the error of
{name}`SqlState.failed` is the reason. Proof sketch: split on the ROLLBACK test and the
snapshot; each branch is the failure, or the pending result that carries its reason. -/
theorem SqlState.failed_error (state : SqlState) (position : Nat) (reason : ExecutionError) (database : Database) :
    (state.failed position reason database).error? = some reason := by
  unfold SqlState.failed SqlState.finish
  split <;> (try split) <;> (try split) <;> simp_all [Outcome.error?]

/-- For every state, position, reason other than ROLLBACK and database:
{name}`SqlState.failed` has that database as its visible database, and the saved snapshot
when present, or else that database, as its persisted database. Proof sketch: the
ROLLBACK test fails, so the result is {name}`SqlState.finish` of the failure; split on the
snapshot. -/
theorem SqlState.failed_database (state : SqlState) (position : Nat) (reason : ExecutionError) (database : Database)
    (other : reason ≠ .constraintRollback) :
    (state.failed position reason database).database = database ∧
    (state.failed position reason database).persistedDatabase = state.snapshot.getD database := by
  unfold SqlState.failed
  split
  · contradiction
  · cases h : state.snapshot <;> simp [SqlState.finish, h, Outcome.database, Outcome.persistedDatabase]

/-- For every state, position and database: {name}`SqlState.failed` of a ROLLBACK
failure has the saved snapshot when present, or else that database, as its visible and
its persisted database. Proof sketch: the ROLLBACK test holds; split on the snapshot,
which gives the failure over the snapshot or the finished failure. -/
theorem SqlState.failed_rollback (state : SqlState) (position : Nat) (database : Database) :
    (state.failed position .constraintRollback database).database = state.snapshot.getD database ∧
    (state.failed position .constraintRollback database).persistedDatabase = state.snapshot.getD database := by
  unfold SqlState.failed
  split
  · cases h : state.snapshot <;> simp [SqlState.finish, h, Outcome.database, Outcome.persistedDatabase]
  · contradiction

end Belay.Sqlite.Model
