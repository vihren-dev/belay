import Belay.Sqlite.Model.StepCatalogLiteral

set_option doc.verso true

/-! One SQL step and the resolution state: a step that continues keeps the connection
state in agreement with {lit}`ResolveState.after`, and a halt has an error.
{lit}`CatalogAgreement` folds these over a script. -/

namespace Belay.Sqlite.Model

/-- For every position, statement, list of values, connection states and resolution state: if
the connection state agrees with the resolution state ({name}`SqlState.Agrees`) and
{name}`advance` of the statement with the values continues, then the next connection state agrees with
{name}`ResolveState.after` of the statement. Proof sketch: BEGIN saves the database whose
catalog the resolution saves, COMMIT drops both, ROLLBACK restores the snapshot whose
catalog the resolution restores, a setting pragma keeps the database, and
every other statement follows {name}`literalStep_success_catalog`. -/
theorem advance_agrees {position : Nat} {statement : Resolved.Statement} {parameters : List Value}
    {sql next : SqlState} {state : ResolveState}
    (agrees : sql.Agrees state) (continued : advance position statement parameters sql = .next next) :
    next.Agrees (state.after statement) := by
  obtain ⟨catalog, saved⟩ := agrees
  obtain ⟨transitioned, reached, rfl⟩ := advance_eq_next continued
  clear continued
  cases statement with
  | begin =>
    simp only [advanceWith] at reached
    split at reached
    · cases reached
    · rename_i none_
      cases reached
      rw [none_] at saved
      simp only [Option.map_none] at saved
      simp [SqlState.Agrees, ResolveState.after, ← saved, catalog]
  | commit =>
    simp only [advanceWith] at reached
    split at reached
    · cases reached
    · cases reached
      exact ⟨catalog, rfl⟩
  | rollback =>
    simp only [advanceWith] at reached
    split at reached
    · cases reached
    · rename_i original some_
      cases reached
      rw [some_] at saved
      simp only [Option.map_some] at saved
      simp [SqlState.Agrees, ResolveState.after, ← saved]
  | setting setting on =>
    simp only [advanceWith] at reached
    obtain ⟨result, stepped, rfl⟩ := Conformance.SqlState.publish_next reached
    simp only [SqlState.statementRun, runStatement, step] at stepped
    cases stepped
    cases setting <;> exact ⟨catalog, saved⟩
  | createTable | createView | createIndex | createTrigger | addColumn | rewrite | drop | insert | update | upsert | insertSelect | delete | prepareError
  | query =>
    simp only [advanceWith] at reached
    obtain ⟨result, stepped, rfl⟩ := Conformance.SqlState.publish_next reached
    obtain ⟨changed, control⟩ := literalStep_success_catalog (fun _ _ => by simp) stepped
    rw [state.after_of_isControl control]
    exact ⟨changed.trans (catalog ▸ rfl), saved⟩

/-- For every position, statement, list of values, connection state and outcome: if
{name}`advance` of the statement with the values halts with the outcome, the outcome has an error ({name}`Outcome.error?`). A halt is never a
success and never a pending transaction without an error. Proof sketch: split on the
statement: BEGIN in a transaction finishes a failure, which keeps its error with or
without a snapshot; COMMIT and ROLLBACK without a transaction fail; every other statement
halts only on an error of {lit}`literalStep` ({lit}`SqlState.publish_halt`), whose error
{name}`SqlState.failed_error` keeps. -/
theorem advance_halt_error {position : Nat} {statement : Resolved.Statement} {parameters : List Value} {sql : SqlState}
    {outcome : Outcome} (halted : advance position statement parameters sql = .halt outcome) : outcome.error?.isSome := by
  have finished : ∀ index reason database,
      (sql.finish (.failure index reason database)).error?.isSome := by
    intro index reason database
    cases h : sql.snapshot <;> simp [SqlState.finish, Outcome.error?, h]
  cases statement with
  | begin =>
    simp only [advance, advanceRun, SqlTransition.counted_eq_halt, advanceWith] at halted
    split at halted
    · cases halted; exact finished _ _ _
    · cases halted
  | commit | rollback =>
    simp only [advance, advanceRun, SqlTransition.counted_eq_halt, advanceWith] at halted
    split at halted
    · cases halted; simp [Outcome.error?]
    · cases halted
  | createTable | createView | createIndex | createTrigger | addColumn | rewrite | drop | insert | update | upsert | insertSelect | delete | prepareError
  | query | setting =>
    simp only [advance, advanceRun, SqlTransition.counted_eq_halt, advanceWith] at halted
    obtain ⟨_, _, _, rfl⟩ := Conformance.SqlState.publish_halt halted
    simp [SqlState.failed_error]

end Belay.Sqlite.Model
