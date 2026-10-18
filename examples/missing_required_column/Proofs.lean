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
  have created := effect_createTable_ok 0 database "audit" audit 1
    (by simp [same, Generated.startCatalog]) (by simp [same, length, Generated.startCatalog])
  rw [script_bound, runSqlAt_of_readsClock _ _ _ (by decide)] at run
  simp only [runSql_eq, runSqlFrom_cons, advance_createTable, created, SqlState.publish_ok, runSqlFrom_nil,
    SqlState.finish] at run
  cases run
  rw [same]
  show ¬((Generated.startCatalog.createTable "audit" audit).columnsOf "invoices" =
    some [{ name := "amount", declaredType := some "INTEGER" }, { name := "note", declaredType := some "TEXT" }])
  decide +kernel
end Proofs
