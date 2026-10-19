import Generated
import Belay.Sqlite.SchemaExtensionLaws
import SqliteVerifier.SchemaProjection

set_option doc.verso true

/-! Prove successful default initialization for every admitted invoice table. -/
namespace Proofs
open Belay.Sqlite SqliteVerifier

/-- The resolved addition binds the exact default and NOT NULL metadata in the contract.
The proof reduces the sealed generated statement. -/
theorem script_bound : Generated.resolved = [.addColumn 0 Requirements.priority] := by rfl

/-- The resulting catalog is the starting catalog with the priority column appended.
The proof reduces the sealed generated catalogs. -/
theorem catalog_bound : Generated.nextCatalog =
    Generated.startCatalog.addColumn 0 Requirements.priority := by rfl

/-- The literal default reads as integer seven. The kernel computes the default reader. -/
theorem default_value : readDefaultValue Requirements.priority = .ok (.integer 7) := by rfl

/-- The default is a literal, not a time keyword, so ADD COLUMN does not depend on the
clock. The kernel computes the check. -/
theorem constant_default : Requirements.priority.clockDefault = false := by rfl

/-- For every admitted starting database, the generated migration succeeds and
preserves every invoice rowid and amount under the exact resulting catalog.
The proof applies {name}`SqliteVerifier.VerificationConditions.ofSchemaProjection`:
the script is one ADD COLUMN, the invoice table stays at position 0 and covers the
amount, and ADD COLUMN succeeds with the literal default seven
({name}`effect_addColumn_ok`). No starting row count or amount is assumed. -/
theorem migrationCorrect : Generated.expected := by
  have startValid : Generated.startCatalog.Valid Generated.profile.limits := by decide +kernel
  have nextValid : Generated.nextCatalog.Valid Generated.profile.limits := by decide +kernel
  apply VerificationConditions.ofSchemaProjection (position := 0)
  · exact ⟨Generated.startCatalog.emptyDatabase, Catalog.emptyDatabase_conforms startValid, trivial⟩
  · intros; trivial
  · simp [SchemaOnly, script_bound]
  · simp [ModeledDefinitions, script_bound, default_value, Except.toOption, constant_default]
  · decide +kernel
  · decide +kernel
  · intro database admitted
    obtain ⟨table, present, shape, _⟩ := admitted.1.table (position := 0) (by rfl)
    exact ⟨table, present, fun name member => by
      simp only [List.mem_singleton] at member
      subst name
      exact ⟨0, by rw [shape]; decide +kernel⟩⟩
  · intro database admitted
    obtain ⟨table, present, _, _⟩ := admitted.1.table (position := 0) (by rfl)
    have conforms : Conforms Generated.profile Generated.nextCatalog
        (database.addColumn 0 Requirements.priority (.integer 7)) := by
      rw [catalog_bound]
      exact admitted.1.addColumn (.integer 7) present (catalog_bound ▸ nextValid)
    refine ⟨database.addColumn 0 Requirements.priority (.integer 7), ?_, conforms, ?_⟩
    · simp only [runSql_eq, script_bound, runSqlFrom_cons, advance_addColumn,
        effect_addColumn_ok 0 present constant_default default_value rfl (by simp [Requirements.priority]),
        SqlState.publish_ok, runSqlFrom_nil]
      rfl
    · rw [conforms.1]
      change Generated.nextCatalog.columnsOf (name! "invoices") = some [Requirements.amount, Requirements.priority]
      decide +kernel
  · intro _; rfl
  · intro _ _; trivial

#print axioms migrationCorrect
end Proofs
