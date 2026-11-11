import SchemaStepLaws

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! A fixture module of {lit}`tests/surface_schema_script_test.py`: the laws of CREATE TABLE and the failure laws of
CREATE TABLE and DROP TABLE (ADR 0017, S6, task {lit}`20261027-schema-script-laws`) on the database of
{lit}`SchemaStepLaws`. The new table is appended and the other tables keep their rows. A statement that SQLite refuses
changes nothing. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace SchemaCreateExamples
open SchemaStepLaws


/-- The statement that creates the table {lit}`q` beside the parent and the child. -/
def createQ : Syntax.Statement := statementOf (sql r"CREATE TABLE q(id INTEGER PRIMARY KEY, v TEXT);")

/-- The statement that creates a table with the name of the parent. -/
def createP : Syntax.Statement := statementOf (sql r"CREATE TABLE p(id INTEGER);")

/-- The statement {lean}`createQ` creates the table {lit}`q` at position 2. -/
theorem createQ_resolves : resolvesShape start createQ (.createTable 2 (name! "q")) = true := by decide +kernel

/-- Success and frame law of CREATE TABLE: the new table is appended at position 2, the catalog and the row lists
keep their alignment, and the parent and the child are found at their positions with their rows. Proof sketch:
{name}`runScriptStep_createTable` and {name}`runScriptStep_createTable_frame` with the resolution of the statement as
a CREATE TABLE at position 2. -/
theorem create_appends_and_keeps : ∀ output next others, stepOf start createQ = .continued output next others →
    output.isError = false ∧ next.state.database.catalog.length = 3 ∧ next.state.database.rows.length = 3 ∧
    foundRows next.state.database (name! "p") = foundRows start.state.database (name! "p") ∧
    foundRows next.state.database (name! "c") = foundRows start.state.database (name! "c") := by
  intro output next others step
  obtain ⟨table, after, found⟩ := resolvesShape_createTable createQ_resolves
  obtain ⟨noError, -, target, aligned, nextEq⟩ := runScriptStep_createTable found step
  have frame (name : Identifier) (position : Nat) (existing : Table)
      (present : start.state.database.tableNamed name = some (position, existing)) :
      next.state.database.tableNamed name = some (position, existing) :=
    runScriptStep_createTable_frame found step present
  refine ⟨noError, ?_, ?_, ?_, ?_⟩
  · rw [nextEq]; simpa [Catalog.createTable] using (by decide +kernel : start.state.database.catalog.length = 2)
  · rw [nextEq]; simpa using (by decide +kernel : start.state.database.rows.length = 2)
  · obtain ⟨existing, present⟩ := tableNamed_exists (database := start.state.database) (name := name! "p")
      (position := 0) (by decide +kernel)
    unfold foundRows
    rw [frame _ _ _ present, present]
  · obtain ⟨existing, present⟩ := tableNamed_exists (database := start.state.database) (name := name! "c")
      (position := 1) (by decide +kernel)
    unfold foundRows
    rw [frame _ _ _ present, present]

/-- Failure law of CREATE TABLE: a CREATE TABLE of a name in use fails with an error output, and the step changes
nothing: the connection after it is the connection before. The kernel shows that the step fails. Proof sketch:
{name}`runScriptStep_createTable_failed`. -/
theorem create_existing_keeps_the_connection : outputOf start createP = some (.error 1) ∧
    ∀ output next others, stepOf start createP = .continued output next others →
      output.isError = true → others = [] ∧ next = start := by
  refine ⟨by decide +kernel, fun output next others step failed => ?_⟩
  obtain ⟨created, columns, constraints, options, form⟩ : ∃ created columns constraints options,
      createP = .createTable created columns constraints options := ⟨_, _, _, _, rfl⟩
  rw [form] at step
  exact runScriptStep_createTable_failed step failed

/-- Failure law of DROP TABLE with foreign keys off: the drop of a table that does not exist fails and changes
nothing. Proof sketch: {name}`runScriptStep_dropTable_off_failed`. -/
theorem drop_missing_keeps_the_connection :
    outputOf start (.dropTable (name! "zz") false) = some (.error 1) ∧
    ∀ output next others, stepOf start (.dropTable (name! "zz") false) = .continued output next others →
      output.isError = true → others = [] ∧ next = start := by
  refine ⟨by decide +kernel, fun output next others step failed => ?_⟩
  exact runScriptStep_dropTable_off_failed (connection := start) (by decide +kernel) step failed


#print axioms create_appends_and_keeps
#print axioms create_existing_keeps_the_connection
#print axioms drop_missing_keeps_the_connection

end SchemaCreateExamples
