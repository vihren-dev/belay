import SqliteVerifier.Library
import Belay.Sqlite.SchemaExtension
import Belay.Sqlite.SchemaClock

set_option doc.verso true

/-! Engineering example: arbitrary stored amounts survive a column addition and
new table. This is a complete VC proof, not a real-pilot acceptance claim. The
catalogs and the resolved script are those that resolution computes for
{lit}`CREATE TABLE invoices(amount INTEGER)` and the migration
{lit}`ALTER TABLE invoices ADD COLUMN note TEXT; CREATE TABLE audit(message TEXT);`. -/

open Belay.Sqlite

namespace SqliteVerifier.Demonstration

/-- The field whose values and row identities are protected by the requirements. -/
def amount : CatalogColumn := { name := "amount", declaredType := some "INTEGER" }
/-- Nullable annotation introduced by the candidate migration. -/
def note : CatalogColumn := { name := "note", declaredType := some "TEXT" }
/-- New table's unprotected field. -/
def message : CatalogColumn := { name := "message", declaredType := some "TEXT" }
/-- Accepted current catalog; rows remain universally quantified. -/
def startCatalog : Catalog := [{ name := "invoices", entry := .table { columns := [amount] } }]
/-- Catalog of the committed prefix after its first successful statement. -/
def middleCatalog : Catalog := [{ name := "invoices", entry := .table { columns := [amount, note] } }]
/-- The resulting catalog includes an independent empty audit table. -/
def nextCatalog : Catalog := middleCatalog ++ [{ name := "audit", entry := .table { columns := [message] } }]
/-- Two resolved statements show ordering rather than assuming file-level atomicity. -/
def script : List Resolved.Statement := [.addColumn 0 note, .createTable 1 "audit" { columns := [message] }]
/-- The same contract can be reused with independently checked additive scripts. -/
def requirements : LogicalContract LogicalRows where
  valid := fun _ => True
  change := Eq
  catalogRequirement catalog := catalog.columnsOf "invoices" = some [amount, note]
  failure := fun before _ _ after => before = after
  applicability := requiresSuccess
/-- Current meaning includes every stored invoice and its actual amount. -/
def current (profile : Profile) : Interpretation LogicalRows :=
  projectedInterpretation profile startCatalog "invoices" ["amount"]
/-- Resulting meaning reads the same protected projection from resulting storage. -/
def next (profile : Profile) : Interpretation LogicalRows :=
  projectedInterpretation profile nextCatalog "invoices" ["amount"]

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
    middleCatalog.createTable "audit" { columns := [message] } = nextCatalog := by
  decide +kernel

/-- The database after {name}`script`: the note column added to the invoices, then the
empty audit table. -/
def migrated (database : Database) : Database :=
  { catalog := (database.addColumn 0 note .null).catalog.createTable "audit" { columns := [message] },
    rows := (database.addColumn 0 note .null).rows ++ [[]] }

/-- For every profile and admitted database, {name}`script` succeeds with
{name}`migrated`. The proof computes the two steps: ADD COLUMN finds the invoice table,
and CREATE TABLE finds the end of the catalog at position 1. -/
theorem script_runs (admitted : Admitted profile startCatalog (fun _ => True) database) :
    runSql script database = .success (migrated database) := by
  obtain ⟨same, length, table, present, _, _⟩ := admitted_invoices admitted
  have middleLength : (database.addColumn 0 note .null).catalog.length = 1 ∧
      (database.addColumn 0 note .null).rows.length = 1 := by
    simp [Database.addColumn, Catalog.length_addColumn, same, length, startCatalog]
  have added : step 0 (.addColumn 0 note) database 0 = .success (database.addColumn 0 note .null) := by
    simp [step, present, CatalogColumn.clockDefault, readDefaultValue, note]
  have created : step 0 (.createTable 1 "audit" { columns := [message] }) (database.addColumn 0 note .null) 1 =
      .success (migrated database) := by
    simp [step, middleLength, migrated]
  simp [runSql, runSqlFrom, advance, literalStep, Resolved.Statement.unclock, SqlState.finish, script, added, created]

/-- The complete {name}`VerificationConditions` hold for the supplied catalogs,
script and preservation contract, for every admitted starting database and every
profile that allows two columns. The proof constructs a starting witness and
sound representations, proves support, then computes the two successful
statements and preserves the invoice projection. -/
theorem migrationCorrect (profile : Profile) (columns : 2 ≤ profile.limits.columns) :
    VerificationConditions startCatalog script (fun _ => True)
      requirements (current profile) (next profile) unreachableFailures profile := by
  obtain ⟨startValid, middleValid, nextValid⟩ := catalogs_valid columns
  apply VerificationConditions.of_runSql
  · exact ⟨startCatalog.emptyDatabase, Catalog.emptyDatabase_conforms startValid, trivial⟩
  · exact projectedInterpretation_sound requirements profile startCatalog "invoices" ["amount"] (by intros; trivial)
  · exact projectedInterpretation_sound requirements profile nextCatalog "invoices" ["amount"] (by intros; trivial)
  · exact unreachableFailures_sound requirements profile
  · intro database admitted
    obtain ⟨_, _, table, present, shape, _⟩ := admitted_invoices admitted
    exact ⟨admitted.1, 0, table, by decide +kernel, present, fun name member => by
      simp only [List.mem_singleton] at member
      subst name
      exact ⟨0, by rw [shape]; decide +kernel⟩⟩
  · intro database _
    exact SupportedSql.schemaOnly (by simp [SchemaOnly, script])
      (by simp [ModeledDefinitions, script, CatalogTable.plain, CatalogColumn.plain, readDefaultValue, Except.toOption, note, message])
  · intro database admitted
    obtain ⟨same, length, table, present, shape, valid⟩ := admitted_invoices admitted
    obtain ⟨toMiddle, toNext⟩ := catalog_steps
    let middle := database.addColumn 0 note .null
    have middleConforms : Conforms profile middleCatalog middle := by
      have extended := admitted.1.addColumn .null present (column := note) (by rw [toMiddle]; exact middleValid)
      rwa [toMiddle] at extended
    have finalConforms : Conforms profile nextCatalog (migrated database) := by
      have extended := middleConforms.createTable "audit" { columns := [message] } (by rw [toNext]; exact nextValid)
      rwa [toNext] at extended
    have executed := script_runs admitted
    rw [executed]
    refine ⟨trivial, ?_⟩
    intro original originalRead
    have covered : Covers table ["amount"] := by
      intro name member
      simp only [List.mem_singleton] at member
      subst name
      exact ⟨0, by rw [shape]; decide +kernel⟩
    have growth : TableExtends table (table.appendColumns [(note, .null)]) := ⟨[(note, .null)], rfl⟩
    have sameProjection := growth.project (fun row member => (valid.2 row member).2.1) covered
    have stored : (migrated database).table 0 = some (table.appendColumns [(note, .null)]) :=
      Database.table_createTable "audit" { columns := [message] } (Database.table_addColumn note .null present)
    have required : requirements.catalogRequirement (migrated database).catalog := by
      rw [finalConforms.1]
      show nextCatalog.columnsOf "invoices" = some [amount, note]
      decide +kernel
    refine ⟨⟨finalConforms, 0, table.appendColumns [(note, .null)], by decide +kernel, stored, growth.covers covered⟩,
      required, table.project ["amount"], ?_, ?_⟩
    · have located : tablePosition nextCatalog "invoices" = some 0 := by decide +kernel
      simpa [next, projectedInterpretation, observeTable, located, stored] using congrArg some sameProjection
    · have located : tablePosition startCatalog "invoices" = some 0 := by decide +kernel
      simpa [current, projectedInterpretation, observeTable, located, present, requirements] using originalRead.symm
  · decide

#print axioms migrationCorrect

end SqliteVerifier.Demonstration

/-!
The engineering example adds a nullable invoice note and creates an audit
table. Its theorem covers arbitrary admitted stored invoice data under every
profile that allows two columns:

```lean
open Belay.Sqlite SqliteVerifier
example (profile : Profile) (columns : 2 ≤ profile.limits.columns) :
    VerificationConditions Demonstration.startCatalog
      Demonstration.script (fun _ => True) Demonstration.requirements
      (Demonstration.current profile) (Demonstration.next profile) unreachableFailures profile :=
  Demonstration.migrationCorrect profile columns
```
-/
