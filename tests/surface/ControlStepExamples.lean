import SchemaStepLaws

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! A fixture module of {lit}`tests/surface_schema_script_test.py`: the step and frame laws of BEGIN, COMMIT and the
pragmas {lit}`foreign_keys` and {lit}`foreign_key_check` (ADR 0017, S6, task {lit}`20261027-schema-script-laws`) on
the database of {lit}`SchemaStepLaws`. Each example resolves the statement on a connection, takes the step, and reads
the failure law, the success law and the frame law from the general theorem: a table found by name keeps its rows
whatever the statement does to the transaction or to the settings. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace ControlStepExamples
open SchemaStepLaws

/-- The statement {lit}`BEGIN`. -/
def beginStatement : Syntax.Statement := statementOf (sql r"BEGIN;")

/-- The statement {lit}`COMMIT`. -/
def commitStatement : Syntax.Statement := statementOf (sql r"COMMIT;")

/-- The statement {lit}`PRAGMA foreign_keys = ON`. -/
def enforceStatement : Syntax.Statement := statementOf (sql r"PRAGMA foreign_keys = ON;")

/-- The statement {lit}`PRAGMA foreign_key_check`. -/
def checkStatement : Syntax.Statement := statementOf (sql r"PRAGMA foreign_key_check;")

/-- The script text of the pragma is the setting of {lit}`foreign_keys` at the value on. -/
theorem enforceStatement_parses : enforceStatement = .pragma (.setting .foreignKeys (some true)) := rfl

/-- The script text of the check is the pragma that only reads. -/
theorem checkStatement_parses : checkStatement = .pragma (.foreignKeyCheck none) := rfl

/-- The connection inside a transaction: the connection after BEGIN. -/
def inTransaction : Connection := ((afterStep start beginStatement).getD start)

/-- BEGIN resolves to BEGIN. -/
theorem begin_resolves : resolvesTo start beginStatement .begin = true := by decide +kernel

/-- COMMIT resolves to COMMIT. -/
theorem commit_resolves : resolvesTo start commitStatement .commit = true := by decide +kernel

/-- Success and frame law of BEGIN outside a transaction: the step has no error output, and the connection after it
holds the database of before as its snapshot and as its database, so the child is found by its name with its rows.
Proof sketch: {name}`runScriptStep_begin_idle` and {name}`runScriptStep_begin_frame`. -/
theorem begin_snapshots_the_database : ∀ output next others, stepOf start beginStatement = .continued output next others →
    output.isError = false ∧ others = [] ∧ next.state.snapshot = some start.state.database ∧
      foundRows next.state.database (name! "c") = foundRows start.state.database (name! "c") := by
  intro output next others step
  obtain ⟨after, found⟩ := resolvesTo_sound begin_resolves
  obtain ⟨noError, single, nextEq⟩ := runScriptStep_begin_idle found rfl step
  refine ⟨noError, single, by rw [nextEq], ?_⟩
  rw [runScriptStep_begin_frame found step]

/-- The kernel shows that the first BEGIN continues, so that {lean}`inTransaction` has a snapshot. -/
theorem inTransaction_has_snapshot : inTransaction.state.snapshot = some start.state.database := by decide +kernel

/-- Failure law of BEGIN inside a transaction: the step fails and the connection is the same. The kernel shows that
the step fails. Proof sketch: {name}`runScriptStep_begin_active`. -/
theorem begin_active_keeps_the_connection : outputOf inTransaction beginStatement = some (.error 1) ∧
    ∀ output next others, stepOf inTransaction beginStatement = .continued output next others →
      output.isError = true ∧ others = [] ∧ next = inTransaction := by
  refine ⟨by decide +kernel, fun output next others step => ?_⟩
  obtain ⟨after, found⟩ : ∃ after, resolveStatement runContext inTransaction.resolveState beginStatement = .ok (.begin, after) :=
    resolvesTo_sound (by decide +kernel)
  exact runScriptStep_begin_active found inTransaction_has_snapshot step

/-- Success law of COMMIT inside a transaction: no error output, the snapshot is gone and the database is the same.
Proof sketch: {name}`runScriptStep_commit_active` and {name}`runScriptStep_commit_frame`. -/
theorem commit_active_closes : ∀ output next others, stepOf inTransaction commitStatement = .continued output next others →
    output.isError = false ∧ next.state.snapshot = none ∧
      foundRows next.state.database (name! "c") = foundRows start.state.database (name! "c") := by
  intro output next others step
  obtain ⟨after, found⟩ : ∃ after, resolveStatement runContext inTransaction.resolveState commitStatement = .ok (.commit, after) :=
    resolvesTo_sound (by decide +kernel)
  obtain ⟨noError, -, nextEq⟩ := runScriptStep_commit_active found inTransaction_has_snapshot step
  refine ⟨noError, by rw [nextEq], ?_⟩
  rw [runScriptStep_commit_frame found step]
  have same : inTransaction.state.database = start.state.database := by decide +kernel
  rw [same]

/-- Failure law of COMMIT outside a transaction: the step fails and the connection is the same. Proof sketch:
{name}`runScriptStep_commit_idle`. -/
theorem commit_idle_keeps_the_connection : outputOf start commitStatement = some (.error 1) ∧
    ∀ output next others, stepOf start commitStatement = .continued output next others →
      output.isError = true ∧ others = [] ∧ next = start := by
  refine ⟨by decide +kernel, fun output next others step => ?_⟩
  obtain ⟨after, found⟩ := resolvesTo_sound commit_resolves
  exact runScriptStep_commit_idle found rfl step

/-- Success and frame law of {lit}`PRAGMA foreign_keys = ON` outside a transaction: enforcement turns on and the
database is the same. Proof sketch: {name}`runScriptStep_pragma_foreignKeys` and {name}`runScriptStep_setting_frame`. -/
theorem pragma_turns_enforcement_on : ∀ output next others, stepOf start enforceStatement = .continued output next others →
    output.isError = false ∧ next.foreignKeys = true ∧
      foundRows next.state.database (name! "c") = foundRows start.state.database (name! "c") := by
  intro output next others step
  obtain ⟨resolved, after, found⟩ := resolves_sound (connection := start) (statement := enforceStatement) (by decide +kernel)
  rw [enforceStatement_parses] at found step
  obtain ⟨noError, -, nextEq⟩ := runScriptStep_pragma_foreignKeys found step
  refine ⟨noError, by rw [nextEq]; rfl, ?_⟩
  rw [nextEq]

/-- Law of {lit}`PRAGMA foreign_keys = ON` inside a transaction: SQLite ignores the pragma, enforcement stays off.
Proof sketch: {name}`runScriptStep_pragma_foreignKeys` with the snapshot of the connection. -/
theorem pragma_inside_a_transaction_is_ignored : ∀ output next others,
    stepOf inTransaction enforceStatement = .continued output next others → next.foreignKeys = false := by
  intro output next others step
  obtain ⟨resolved, after, found⟩ := resolves_sound (connection := inTransaction) (statement := enforceStatement)
    (by decide +kernel)
  rw [enforceStatement_parses] at found step
  obtain ⟨-, -, nextEq⟩ := runScriptStep_pragma_foreignKeys found step
  rw [nextEq]
  have snapshot : inTransaction.state.snapshot.isSome = true := by rw [inTransaction_has_snapshot]; rfl
  simp only [snapshot, ite_true]
  decide +kernel

/-- Law of {lit}`PRAGMA foreign_key_check`: the pragma reads and changes nothing, not even the counters. Proof
sketch: {name}`runScriptStep_pragma_keeps`. -/
theorem check_keeps_the_connection : ∀ output next others,
    stepOf enforcing checkStatement = .continued output next others → others = [] ∧ next = enforcing := by
  intro output next others step
  obtain ⟨resolved, after, found⟩ := resolves_sound (connection := enforcing) (statement := checkStatement) (by decide +kernel)
  rw [checkStatement_parses] at found step
  exact runScriptStep_pragma_keeps (by rfl) found step

#print axioms begin_snapshots_the_database
#print axioms begin_active_keeps_the_connection
#print axioms commit_active_closes
#print axioms commit_idle_keeps_the_connection
#print axioms pragma_turns_enforcement_on
#print axioms pragma_inside_a_transaction_is_ignored
#print axioms check_keeps_the_connection

end ControlStepExamples
