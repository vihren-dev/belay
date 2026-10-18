import Belay.Sqlite.SqlLaws
import Belay.Sqlite.SqlExecution
import Belay.Sqlite.DatabaseLaws

set_option doc.verso true

/-! SQLite model laws describe transaction rollback, statement failure and
row preservation when a column is added. -/
set_option maxHeartbeats 2000000
namespace Belay.Sqlite.Conformance

/-- Each statement in the body is non-control and succeeds at its position, at the clock
value of the clock assignment for that position, as {name}`advance` runs it. The remaining
body starts from its resulting database. An empty body requires nothing of the database.
Use this predicate to state successful-body laws. -/
inductive SuccessfulBody (clock : Nat → Int) : Nat → List Resolved.Statement → Database → Prop where
  /-- Every position and database admit an empty successful body; no statement premise is required. -/
  | nil : SuccessfulBody clock position [] database
  /-- A non-control statement that succeeds, followed by a successful tail, forms a successful body. -/
  | cons (ordinary : statement.isControl = false)
      (success : literalStep (clock position) statement database = .ok next)
      (tail : SuccessfulBody clock (position + 1) rest next) :
      SuccessfulBody clock position (statement :: rest) database

/-- For any clock assignment, position, body, current database and original snapshot, if
{name}`SuccessfulBody` holds, running the body followed by ROLLBACK with that
snapshot and clock assignment returns success with exactly the original database.

The proof inducts over the successful body. Each non-control step preserves
the snapshot; the final ROLLBACK restores it. -/
theorem body_rollback (success : SuccessfulBody clock position body database) :
    runSqlFrom position (body ++ [.rollback]) { database, snapshot := some original, clock } =
      .success original := by
  induction success with
  | nil => simp [runSqlFrom, advance, SqlState.finish]
  | @cons position statement database next rest ordinary success tail ih =>
    cases statement <;> simp_all [Resolved.Statement.isControl, runSqlFrom, advance, SqlState.publish]

/-- For any body and database, if {name}`SuccessfulBody` holds at position 1 at the clock
value 0, BEGIN followed by the body and ROLLBACK returns success with that database.

The proof unfolds BEGIN and applies {name}`body_rollback` with the initial
database as the transaction snapshot. -/
theorem rollback (success : SuccessfulBody (fun _ => 0) 1 body database) :
    runSql (.begin :: body ++ [.rollback]) database = .success database := by
  simpa [runSql, runSqlFrom, advance] using body_rollback (original := database) success

/-- For every state, position, effect and outcome: if {name}`SqlState.publish` of the
effect halts with the outcome, the effect is an error with some reason and reached
database, and the outcome is {name}`SqlState.failed` of that reason with the reached
database for a FAIL failure and the state's database for every other reason. -/
theorem SqlState.publish_halt {state : SqlState} {position : Nat} {effect : Effect} {outcome : Outcome}
    (halted : state.publish position effect = .halt outcome) :
    ∃ reason reached, effect = .error (reason, reached) ∧
      outcome = state.failed position reason (if reason = .constraintFail then reached else state.database) := by
  cases effect with
  | ok database => simp [SqlState.publish] at halted
  | error failure =>
    obtain ⟨reason, reached⟩ := failure
    simp only [SqlState.publish, SqlTransition.halt.injEq] at halted
    exact ⟨reason, reached, rfl, halted.symm⟩

/-- For every state, position, effect and next state: if {name}`SqlState.publish` of the
effect continues with the next state, the effect succeeds with some database, and the
next state is the state with that database. -/
theorem SqlState.publish_next {state next : SqlState} {position : Nat} {effect : Effect}
    (continued : state.publish position effect = .next next) :
    ∃ database, effect = .ok database ∧ next = { state with database } := by
  cases effect with
  | ok database =>
    simp only [SqlState.publish, SqlTransition.next.injEq] at continued
    exact ⟨database, rfl, continued.symm⟩
  | error failure => simp [SqlState.publish] at continued

/-- For any position, statement, state and outcome, if {name}`advance` halts with that
outcome and its error is neither a FAIL failure ({name}`ExecutionError.constraintFail`)
nor a ROLLBACK failure ({name}`ExecutionError.constraintRollback`), its visible database
equals the state's current database. Its persisted database equals the saved snapshot
when present, and otherwise the current database. For FAIL and ROLLBACK the formula
says nothing; {lit}`constraint_rollback` states ROLLBACK.

The proof splits on the statement and snapshot; an ordinary statement halts through
{name}`SqlState.publish_halt`, which keeps the state's database for these errors. -/
theorem statement_atomicity (halted : advance position statement state = .halt outcome)
    (atomic : outcome.error? ≠ some .constraintFail ∧ outcome.error? ≠ some .constraintRollback) :
    outcome.database = state.database ∧
    outcome.persistedDatabase = state.snapshot.getD state.database := by
  cases statement <;> simp only [advance] at halted
  all_goals try (solve | (clear atomic; cases h : state.snapshot <;> simp_all [SqlState.finish,
    Outcome.database, Outcome.persistedDatabase, Option.getD]))
  all_goals first
    | (obtain ⟨reason, reached, _, rfl⟩ := SqlState.publish_halt halted
       have notFail : reason ≠ .constraintFail :=
         fun failed => atomic.1 (by subst failed; exact SqlState.failed_error _ _ _ _)
       have notRollback : reason ≠ .constraintRollback :=
         fun rolled => atomic.2 (by subst rolled; exact SqlState.failed_error _ _ _ _)
       simp only [notFail, if_false]
       exact SqlState.failed_database _ _ _ _ notRollback)
    | (clear atomic; cases hs : state.snapshot <;>
       simp_all [SqlState.finish, Outcome.database, Outcome.persistedDatabase, Option.getD] <;>
       subst halted <;> simp)

/-- For any position, statement, state and outcome, if {name}`advance` halts with that
outcome and its error is a ROLLBACK failure ({name}`ExecutionError.constraintRollback`),
its visible and its persisted database are the saved snapshot when present, and
otherwise the current database: the transaction of the snapshot is rolled back.

The proof splits on the statement and snapshot; an ordinary statement halts through
{name}`SqlState.publish_halt`, which gives a ROLLBACK failure the state's database. -/
theorem constraint_rollback (halted : advance position statement state = .halt outcome)
    (rolled : outcome.error? = some .constraintRollback) :
    outcome.database = state.snapshot.getD state.database ∧
    outcome.persistedDatabase = state.snapshot.getD state.database := by
  cases statement <;> simp only [advance] at halted
  all_goals try (solve | cases h : state.snapshot <;> simp_all [SqlState.finish,
    Outcome.database, Outcome.persistedDatabase, Option.getD, Outcome.error?])
  all_goals first
    | (obtain ⟨reason, reached, _, rfl⟩ := SqlState.publish_halt halted
       rw [SqlState.failed_error] at rolled
       cases rolled
       exact SqlState.failed_rollback _ _ _)
    | (cases hs : state.snapshot <;>
       simp_all [SqlState.finish, Outcome.database, Outcome.persistedDatabase, Option.getD, Outcome.error?] <;>
       subst halted <;> simp_all)

/-- For any position, table position, column without a time default
({name}`CatalogColumn.clockDefault`) and states, if ADD COLUMN advances to the next state,
some table exists at that table position in the original state.
The next database contains that table with the column appended. This table has
the same row count and rowids, and each original row gains the affinity-applied
value returned by {name}`readDefaultValue`.

The proof follows the successful ADD branch and unfolds column extension
and its row mapping. -/
theorem add_column_shape (constant : column.clockDefault = false)
    (success : advance position (.addColumn target column) state = .next next) :
    ∃ table value, state.database.table target = some table ∧
      readDefaultValue column = .ok value ∧
      next.database.table target = some (table.appendColumns [(column, value)]) ∧
      (table.appendColumns [(column, value)]).rows.length = table.rows.length ∧
      (table.appendColumns [(column, value)]).rows.map Row.rowid = table.rows.map Row.rowid ∧
      (table.appendColumns [(column, value)]).rows.map Row.values =
        table.rows.map (fun row => row.values ++ [storeValue column.affinity value]) := by
  simp only [advance, literalStep, step, SqlState.publish] at success
  repeat (split at * <;> simp_all)
  all_goals subst_vars
  all_goals simp_all [Database.table_addColumn, Table.appendColumns, Row.appendValues, List.map_map]

#print axioms rollback
#print axioms statement_atomicity
#print axioms constraint_rollback
#print axioms add_column_shape
end Belay.Sqlite.Conformance
