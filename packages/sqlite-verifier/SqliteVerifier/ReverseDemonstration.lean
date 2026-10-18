import SqliteVerifier.Demonstration

set_option doc.verso true

/-! An independently checked migration reuses the exact same logical contract
and initial interpretation; the proof accounts for its changed statement order.
The resolved script is the one for
{lit}`CREATE TABLE audit(message TEXT); ALTER TABLE invoices ADD COLUMN note TEXT;`. -/

open Belay.Sqlite

namespace SqliteVerifier.Demonstration

/-- Create the independent audit table before extending existing invoices. -/
def reverseScript : List Resolved.Statement :=
  [.createTable 1 "audit" { columns := [message] }, .addColumn 0 note]

/-- For every profile and every database admitted by {name}`startCatalog` and the
true condition, {name}`reverseScript` and {name}`script` have equal computed SQL
outcomes. There is no claim for unadmitted databases. The proof computes both
successful orders; ADD COLUMN and CREATE TABLE commute
({name}`Database.addColumn_createTable`). -/
theorem reverse_runs (database : Database) (admitted : Admitted profile startCatalog (fun _ => True) database) :
    runSql reverseScript database = runSql script database := by
  obtain ⟨same, length, table, present, _, _⟩ := admitted_invoices admitted
  let created : Database :=
    { catalog := database.catalog.createTable "audit" { columns := [message] }, rows := database.rows ++ [[]] }
  have audit : step 0 (.createTable 1 "audit" { columns := [message] }) database 0 = .success created := by
    simp [step, same, length, startCatalog, created]
  have invoice : created.table 0 = some table := Database.table_createTable _ _ present
  have added : step 0 (.addColumn 0 note) created 1 = .success (created.addColumn 0 note .null) := by
    simp [step, invoice, CatalogColumn.clockDefault, readDefaultValue, note]
  have reversed : runSql reverseScript database = .success (created.addColumn 0 note .null) := by
    simp [runSql, runSqlFrom, advance, literalStep, SqlState.finish, reverseScript, audit, added]
  rw [reversed, script_runs admitted, Database.addColumn_createTable database note .null _ _
    (by simp [same, startCatalog]) (by simp [same, length, startCatalog])]
  rfl

/-- The complete {name}`VerificationConditions` hold for {name}`reverseScript` with
the same approved catalogs, contract and interpretations, under every profile that
allows two columns. The proof reuses {name}`migrationCorrect` through
{name}`reverse_runs` and separately proves the reordered script supported for
every admitted starting database. -/
theorem reverseMigrationCorrect (profile : Profile) (columns : 2 ≤ profile.limits.columns) :
    VerificationConditions startCatalog reverseScript (fun _ => True)
      requirements (current profile) (next profile) unreachableFailures profile :=
  (migrationCorrect profile columns).congr_runSql
    (fun _ _ => SupportedSql.schemaOnly (by simp [SchemaOnly, reverseScript])
      (by simp [ModeledDefinitions, reverseScript, CatalogTable.plain, CatalogColumn.plain, readDefaultValue, Except.toOption, note, message]))
    reverse_runs (by decide) (by decide)

#print axioms reverseMigrationCorrect

end SqliteVerifier.Demonstration
