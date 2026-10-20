import Belay.Sqlite.Laws
import Belay.Sqlite.Resolution.ResolveStateSpec

set_option doc.verso true

/-! One SQL step and the resolution state: a step that continues keeps the connection
state in agreement with {lit}`ResolveState.after`, and a halt has an error.
{lit}`CatalogAgreement` folds these over a script. -/

namespace Belay.Sqlite

/-- A connection state agrees with a resolution state when the visible database has the
current catalog of the resolution, and an open transaction's snapshot has the saved
catalog: both are absent, or both are present with equal catalogs. -/
def SqlState.Agrees (sql : SqlState) (state : ResolveState) : Prop :=
  sql.database.catalog = state.catalog ∧ sql.snapshot.map (·.catalog) = state.saved

/-- For every clock value, statement, database and result: if {name}`literalStep` succeeds
with the result, then the result's catalog is {name}`Resolved.Statement.applyCatalog` of
the statement on the database's catalog, and the statement is not transaction control.
Proof sketch: CREATE TABLE, CREATE INDEX, ADD COLUMN and DROP call the catalog functions, writes store rows
only ({name}`Database.setRows`), a query returns the database, and every other statement
fails. -/
theorem literalStep_success_catalog {clock : Int} {statement : Resolved.Statement} {database result : Database}
    (success : literalStep clock statement database = .ok result) :
    result.catalog = statement.applyCatalog database.catalog ∧ statement.isControl = false := by
  cases statement with
  | createTable target name table =>
    simp only [literalStep, runStatement, step] at success
    split at success
    · cases success; exact ⟨rfl, rfl⟩
    · cases success
  | addColumn target column =>
    simp only [literalStep, runStatement, step] at success
    split at success
    · cases success
    · repeat' split at success
      all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
  | insert target rows returning subqueries =>
    simp only [literalStep, runStatement, insertOutcome, checkedWrite] at success
    repeat' split at success
    all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
  | upsert target rows clauses returning algorithm subqueries =>
    simp only [literalStep, runStatement] at success
    repeat' split at success
    all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
  | update target assignments filter returning subqueries =>
    simp only [literalStep, runStatement, checkedWrite] at success
    repeat' split at success
    all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
  | delete target filter returning subqueries =>
    simp only [literalStep, runStatement] at success
    split at success
    · cases success
    · cases success; exact ⟨rfl, rfl⟩
  | query query subqueries =>
    simp only [literalStep, runStatement] at success
    cases ran : query.runOn clock database subqueries with
    | none => simp only [ran, queryEffect] at success; cases success; exact ⟨rfl, rfl⟩
    | some pair =>
      obtain ⟨_, run⟩ := pair
      simp only [ran, queryEffect] at success
      repeat' split at success
      all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
  | createIndex target name index =>
    simp only [literalStep, runStatement, step] at success
    repeat' split at success
    all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
  | drop positions =>
    simp only [literalStep, runStatement, step] at success
    cases success; exact ⟨rfl, rfl⟩
  | begin | commit | rollback | prepareError =>
    simp [literalStep, runStatement, step] at success

/-- For every position, statement, connection states and resolution state: if the
connection state agrees with the resolution state ({name}`SqlState.Agrees`) and
{name}`advance` continues, then the next connection state agrees with
{name}`ResolveState.after` of the statement. Proof sketch: BEGIN saves the database whose
catalog the resolution saves, COMMIT drops both, ROLLBACK restores the snapshot whose
catalog the resolution restores, and every other statement follows
{name}`literalStep_success_catalog`. -/
theorem advance_agrees {position : Nat} {statement : Resolved.Statement} {sql next : SqlState} {state : ResolveState}
    (agrees : sql.Agrees state) (continued : advance position statement sql = .next next) :
    next.Agrees (state.after statement) := by
  obtain ⟨catalog, saved⟩ := agrees
  cases statement with
  | begin =>
    simp only [advance, advanceWith] at continued
    split at continued
    · cases continued
    · rename_i none_
      cases continued
      rw [none_] at saved
      simp only [Option.map_none] at saved
      simp [SqlState.Agrees, ResolveState.after, ← saved, catalog]
  | commit =>
    simp only [advance, advanceWith] at continued
    split at continued
    · cases continued
    · cases continued
      exact ⟨catalog, rfl⟩
  | rollback =>
    simp only [advance, advanceWith] at continued
    split at continued
    · cases continued
    · rename_i original some_
      cases continued
      rw [some_] at saved
      simp only [Option.map_some] at saved
      simp [SqlState.Agrees, ResolveState.after, ← saved]
  | createTable | createIndex | addColumn | drop | insert | update | upsert | delete | prepareError | query =>
    simp only [advance, advanceWith] at continued
    obtain ⟨result, stepped, rfl⟩ := Conformance.SqlState.publish_next continued
    obtain ⟨changed, control⟩ := literalStep_success_catalog stepped
    rw [state.after_of_isControl control]
    exact ⟨changed.trans (catalog ▸ rfl), saved⟩

/-- For every position, statement, connection state and outcome: if {name}`advance` halts
with the outcome, the outcome has an error ({name}`Outcome.error?`). A halt is never a
success and never a pending transaction without an error. Proof sketch: split on the
statement: BEGIN in a transaction finishes a failure, which keeps its error with or
without a snapshot; COMMIT and ROLLBACK without a transaction fail; every other statement
halts only on an error of {lit}`literalStep` ({lit}`SqlState.publish_halt`), whose error
{name}`SqlState.failed_error` keeps. -/
theorem advance_halt_error {position : Nat} {statement : Resolved.Statement} {sql : SqlState} {outcome : Outcome}
    (halted : advance position statement sql = .halt outcome) : outcome.error?.isSome := by
  have finished : ∀ index reason database,
      (sql.finish (.failure index reason database)).error?.isSome := by
    intro index reason database
    cases h : sql.snapshot <;> simp [SqlState.finish, Outcome.error?, h]
  cases statement with
  | begin =>
    simp only [advance, advanceWith] at halted
    split at halted
    · cases halted; exact finished _ _ _
    · cases halted
  | commit | rollback =>
    simp only [advance, advanceWith] at halted
    split at halted
    · cases halted; simp [Outcome.error?]
    · cases halted
  | createTable | createIndex | addColumn | drop | insert | update | upsert | delete | prepareError | query =>
    simp only [advance, advanceWith] at halted
    obtain ⟨_, _, _, rfl⟩ := Conformance.SqlState.publish_halt halted
    simp [SqlState.failed_error]

end Belay.Sqlite
