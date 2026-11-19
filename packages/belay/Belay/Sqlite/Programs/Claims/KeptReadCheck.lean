import Belay.Sqlite.Programs.Claims.KeptRead
import Belay.Sqlite.Model.Queries.Preparation.OutputTable

set_option doc.verso true

/-! Compute the schema, table and read certificates needed for read preservation. -/

namespace Belay.Sqlite.KeptRead
open Model

/-- Check a single read of the named table against the schema before and after the migration.
The analysis uses the table's original width. A successful check matches both resolved
reads to one certificate and follows the table to its final position. A false result
gives no conclusion. Use the SQL table name, for example {lean}`name! "sessions"`. -/
def preservesCheck (name : Identifier) (schema : Database) (migration query : Script) : Bool :=
  let initial := schema.raw.connection.resolveState
  match query.statements, resolveFrom runContext 0 initial (migration.statements.map Prod.fst) with
  | [(statement, _)], .ok (path, final) =>
    match schema.raw.catalog.findTable name, final.catalog.findTable name,
        resolveStatement runContext initial statement, resolveStatement runContext final statement with
    | some (p, shape), some (q, _), .ok (before, _), .ok (afterRead, _) =>
      match ReadAnalysis.analyze shape.columns.length before with
      | .certified certificate =>
        certificate.position == p && initial.tablePosition path migration.statements.length p == some q &&
          afterRead == (certificate.moved q).statement afterRead.resultNames
      | .unknown _ => false
    | _, _, _, _ => false
  | _, _ => false

/-- If {name}`preservesCheck` passes, the migration preserves the given read on every
database with the given schema, for every complete environment in which the migration
succeeds. For a concrete migration use {lit}`preserves_of_check (name! "sessions") (by decide +kernel)`.
Proof sketch: unpack the two resolutions and lookups, the table check and the read
analysis, then apply {name}`preserves` to those certificates. -/
theorem preserves_of_check (name : Identifier) {schema : Database} {migration query : Script}
    (checked : preservesCheck name schema migration query = true) (readOnly : query.isQuery = true := by check_query) :
    Migration.QueryPreserves (send migration) query (·.HasCatalog schema) readOnly := by
  obtain ⟨statements⟩ := query
  rcases statements with _ | ⟨⟨statement, values⟩, _ | ⟨_, _⟩⟩ <;>
    simp only [preservesCheck] at checked <;> try contradiction
  split at checked <;> try contradiction
  rename_i _ _ _ _ _ _ listed _
  cases listed
  split at checked <;> try contradiction
  split at checked <;> try contradiction
  simp only [Bool.and_eq_true, beq_iff_eq] at checked
  obtain ⟨⟨place, frame⟩, moved⟩ := checked
  apply preserves values readOnly (name := name) (by assumption) (by assumption) (by assumption)
    (by assumption) place frame (by assumption)
  rw [← moved]
  assumption

end Belay.Sqlite.KeptRead
