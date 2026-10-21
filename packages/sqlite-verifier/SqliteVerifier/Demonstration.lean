import SqliteVerifier.Library
import SqliteVerifier.SchemaProjection
import Belay.Sqlite.Model.ScriptLaws
import Belay.Sqlite.Model.SchemaExtensionLaws
import Belay.Sqlite.Model.SchemaClockLaws

set_option doc.verso true

/-! Engineering example: arbitrary stored amounts survive a column addition and
new table. This is a complete VC proof, not a real-pilot acceptance claim. The
catalogs and the resolved script are those that resolution computes for
{lit}`CREATE TABLE invoices(amount INTEGER)` and the migration
{lit}`ALTER TABLE invoices ADD COLUMN note TEXT; CREATE TABLE audit(message TEXT);`. -/

open Belay.Sqlite.Model

namespace SqliteVerifier.Demonstration

/-- The field whose values and row identities are protected by the requirements. -/
def amount : CatalogColumn := { name := (name! "amount"), declaredType := some "INTEGER" }
/-- Nullable annotation introduced by the candidate migration. -/
def note : CatalogColumn := { name := (name! "note"), declaredType := some "TEXT" }
/-- New table's unprotected field. -/
def message : CatalogColumn := { name := (name! "message"), declaredType := some "TEXT" }
/-- Accepted current catalog; rows remain universally quantified. -/
def startCatalog : Catalog := [{ name := (name! "invoices"), entry := .table { columns := [amount] } }]
/-- Catalog of the committed prefix after its first successful statement. -/
def middleCatalog : Catalog := [{ name := (name! "invoices"), entry := .table { columns := [amount, note] } }]
/-- The resulting catalog includes an independent empty audit table. -/
def nextCatalog : Catalog := middleCatalog ++ [{ name := (name! "audit"), entry := .table { columns := [message] } }]
/-- Two resolved statements show ordering rather than assuming file-level atomicity. -/
def script : List Resolved.Statement := [.addColumn 0 note, .createTable 1 (name! "audit") { columns := [message] }]
/-- The same contract can be reused with independently checked additive scripts. -/
def requirements : LogicalContract LogicalRows where
  valid := fun _ => True
  change := Eq
  catalogRequirement catalog := catalog.columnsOf (name! "invoices") = some [amount, note]
  failure := fun before _ _ after => before = after
  applicability := requiresSuccess
/-- Current meaning includes every stored invoice and its actual amount. -/
def current (profile : Profile) : Interpretation LogicalRows :=
  projectedInterpretation profile startCatalog (name! "invoices") [(name! "amount")]
/-- Resulting meaning reads the same protected projection from resulting storage. -/
def next (profile : Profile) : Interpretation LogicalRows :=
  projectedInterpretation profile nextCatalog (name! "invoices") [(name! "amount")]

/-- Limits that allow the two columns of the widest table here; validity under them
carries over to every profile with a larger column limit. -/
def twoColumns : Limits := { Limits.documentedDefaults with columns := 2 }

/-- For every profile that allows two columns, the three catalogs satisfy
{name}`Catalog.Valid`. The proof decides them under {name}`twoColumns` and applies
{name}`Catalog.Valid.mono`. -/
theorem catalogs_valid {profile : Profile} (columns : 2 ≤ profile.limits.columns) :
    startCatalog.Valid profile.limits ∧ middleCatalog.Valid profile.limits ∧ nextCatalog.Valid profile.limits :=
  ⟨Catalog.Valid.mono (limits := twoColumns) (by decide +kernel) columns,
   Catalog.Valid.mono (limits := twoColumns) (by decide +kernel) columns,
   Catalog.Valid.mono (limits := twoColumns) (by decide +kernel) columns⟩

/-- For every profile and admitted database, the database's catalog is
{name}`startCatalog`, it has one row list, and the invoice table at position 0 has exactly
the amount column and is valid. The proof reads them from conformance. -/
theorem admitted_invoices (admitted : Admitted profile startCatalog (fun _ => True) database) :
    database.catalog = startCatalog ∧ database.rows.length = 1 ∧ ∃ table, database.table 0 = some table ∧
      table.shape = { columns := [amount] } ∧ table.Valid := by
  obtain ⟨table, present, shape, valid⟩ := admitted.1.table (position := 0) (by rfl)
  obtain ⟨same, _, length, _⟩ := admitted.1
  exact ⟨same, by simp [length, same, startCatalog], table, present, shape, valid⟩

/-- ADD COLUMN of {name}`note` on {name}`startCatalog` gives {name}`middleCatalog`, and the
CREATE TABLE of the audit table on it gives {name}`nextCatalog`. -/
theorem catalog_steps : startCatalog.addColumn 0 note = middleCatalog ∧
    middleCatalog.createTable (name! "audit") { columns := [message] } = nextCatalog := by
  decide +kernel

/-- The database after {name}`script`: the note column added to the invoices, then the
empty audit table. -/
def migrated (database : Database) : Database :=
  { catalog := (database.addColumn 0 note .null).catalog.createTable (name! "audit") { columns := [message] },
    rows := (database.addColumn 0 note .null).rows ++ [[]] }

/-- For every profile and admitted database, {name}`script` succeeds with
{name}`migrated`. The proof runs the two statements with the script lemmas
({name}`runSqlFrom_cons`, {name}`advance_effect`): ADD COLUMN finds the invoice table
({name}`effect_addColumn_ok`), and CREATE TABLE finds the end of the catalog at position 1
({name}`effect_createTable_ok`). -/
theorem script_runs (admitted : Admitted profile startCatalog (fun _ => True) database) :
    runSql script database = .success (migrated database) := by
  obtain ⟨same, length, table, present, _, _⟩ := admitted_invoices admitted
  have middleLength : (database.addColumn 0 note .null).catalog.length = 1 ∧
      (database.addColumn 0 note .null).rows.length = 1 := by
    simp [Database.addColumn, Catalog.length_addColumn, same, length, startCatalog]
  have added := effect_addColumn_ok 0 present (column := note) (value := .null) rfl rfl rfl (by simp [note])
  have created := effect_createTable_ok 0 (database.addColumn 0 note .null) (name! "audit") { columns := [message] } 1
    middleLength.1.symm (middleLength.2.trans middleLength.1.symm)
  simp only [runSql_eq, script, runSqlFrom_cons, advance_addColumn, advance_createTable, added, created, SqlState.publish_ok,
    runSqlFrom_nil]
  rfl

/-- The complete {name}`VerificationConditions` hold for the supplied catalogs,
script and preservation contract, for every admitted starting database and every
profile that allows two columns. The proof applies
{name}`VerificationConditions.ofSchemaProjection`: the script is schema-only, the invoice
table stays at position 0 and covers the amount, and the two statements succeed
({name}`script_runs`) with a database that conforms to the next catalog. -/
theorem migrationCorrect (profile : Profile) (columns : 2 ≤ profile.limits.columns) :
    VerificationConditions startCatalog script (fun _ => True)
      requirements (current profile) (next profile) unreachableFailures profile := by
  obtain ⟨startValid, middleValid, nextValid⟩ := catalogs_valid columns
  apply VerificationConditions.ofSchemaProjection (position := 0)
  · exact ⟨startCatalog.emptyDatabase, Catalog.emptyDatabase_conforms startValid, trivial⟩
  · intros; trivial
  · simp [SchemaOnly, script]
  · simp [ModeledDefinitions, script, readDefaultValue, Except.toOption,
      note, message]
  · decide +kernel
  · decide +kernel
  · intro database admitted
    obtain ⟨_, _, table, present, shape, _⟩ := admitted_invoices admitted
    exact ⟨table, present, fun name member => by
      simp only [List.mem_singleton] at member
      subst name
      exact ⟨0, by rw [shape]; decide +kernel⟩⟩
  · intro database admitted
    obtain ⟨_, _, table, present, _, _⟩ := admitted_invoices admitted
    obtain ⟨toMiddle, toNext⟩ := catalog_steps
    have middleConforms : Conforms profile middleCatalog (database.addColumn 0 note .null) := by
      have extended := admitted.1.addColumn .null present (column := note) (by rw [toMiddle]; exact middleValid)
      rwa [toMiddle] at extended
    have finalConforms : Conforms profile nextCatalog (migrated database) := by
      have extended := middleConforms.createTable (name! "audit") { columns := [message] } (by rw [toNext]; exact nextValid)
      rwa [toNext] at extended
    refine ⟨migrated database, script_runs admitted, finalConforms, ?_⟩
    rw [finalConforms.1]
    show nextCatalog.columnsOf (name! "invoices") = some [amount, note]
    decide +kernel
  · intro _; rfl
  · intro _ _; trivial

#print axioms migrationCorrect

end SqliteVerifier.Demonstration

/-!
The engineering example adds a nullable invoice note and creates an audit
table. Its theorem covers arbitrary admitted stored invoice data under every
profile that allows two columns:

```lean
open Belay.Sqlite.Model SqliteVerifier
example (profile : Profile) (columns : 2 ≤ profile.limits.columns) :
    VerificationConditions Demonstration.startCatalog
      Demonstration.script (fun _ => True) Demonstration.requirements
      (Demonstration.current profile) (Demonstration.next profile) unreachableFailures profile :=
  Demonstration.migrationCorrect profile columns
```
-/
