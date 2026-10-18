import Generated

/-! A checked refutation identifies the unfulfilled standing catalog requirement. -/
namespace Proofs
open Belay.Sqlite

/-- The table that the migration creates. -/
def audit : CatalogTable := { columns := [{ name := "message", declaredType := some "TEXT" }] }

/-- The generated script creates the audit table and nothing else. -/
theorem script_bound : Generated.resolved = [.createTable 1 "audit" audit] := by rfl

/-- The required invoice.note column is absent from the catalog of every successful
result: for an admitted database, whose catalog is the starting catalog, the only statement
adds the audit table and leaves the invoices unchanged. -/
theorem migrationViolated : ¬Generated.expected := by
  apply SqliteVerifier.violates_required_catalog (successRequired := rfl)
  intro database admitted result run
  obtain ⟨same, _, length, _⟩ := admitted.1
  have created : step (.createTable 1 "audit" audit) database 0 =
      .success { catalog := database.catalog.createTable "audit" audit, rows := database.rows ++ [[]] } := by
    simp only [step]
    simp [same, length, Generated.startCatalog]
  rw [script_bound] at run
  simp [runSqlAt, scriptAtClock, Resolved.Statement.atClock, Resolved.Statement.expressionsAtClock, runSql,
    runSqlFrom, advance, literalStep, created, SqlState.finish] at run
  subst run
  rw [same]
  show ¬((Generated.startCatalog.createTable "audit" audit).columnsOf "invoices" =
    some [{ name := "amount", declaredType := some "INTEGER" }, { name := "note", declaredType := some "TEXT" }])
  decide +kernel
end Proofs
