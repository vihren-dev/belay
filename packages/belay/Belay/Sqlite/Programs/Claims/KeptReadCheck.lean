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

/-- For every schema, migration and single read, a positive check on a reference
script proves preservation of the read when its step agrees with the reference step
on every connection, clock, index and parameter list. The reference can be the read
itself. Proof sketch: the checker supplies the table frame and resolutions of the
reference. Use step agreement to transport its scans to the actual read and apply
{name}`preserves`. -/
theorem preserves_of_check (name : Identifier) {schema : Database} {migration query : Script}
    (reference : Script) (checked : preservesCheck name schema migration reference = true)
    (readOnly : query.isQuery = true := by check_query)
    (same : ∀ statement values, query.statements = [(statement, values)] →
      ∃ compared bindings, reference.statements = [(compared, bindings)] ∧
        ∀ clock index connection parameters,
          runScriptStep runContext clock index connection statement parameters =
            runScriptStep runContext clock index connection compared parameters := by
      intro statement values head
      exact ⟨statement, values, head, fun _ _ _ _ => rfl⟩) :
    Migration.QueryPreserves (send migration) query (·.HasCatalog schema) readOnly := by
  obtain ⟨statements⟩ := query
  rcases statements with _ | ⟨⟨statement, values⟩, _ | ⟨_, _⟩⟩ <;>
    simp only [Script.isQuery] at readOnly <;> try contradiction
  obtain ⟨compared, bindings, head, agrees⟩ := same statement values rfl
  simp only [preservesCheck, head] at checked
  split at checked <;> try contradiction
  rename_i _ _ _ _ _ _ listed _
  cases listed
  split at checked <;> try contradiction
  split at checked <;> try contradiction
  simp only [Bool.and_eq_true, beq_iff_eq] at checked
  obtain ⟨⟨place, frame⟩, moved⟩ := checked
  rename_i certified
  have analyzed := ReadAnalysis.analyze_sound certified
  have scans {witness : ReadCertificate} (valid : witness.Valid) (connection : Connection)
      {names state} (resolved : resolveStatement runContext connection.resolveState compared =
        .ok (witness.statement names, state)) : witness.Scans runContext statement connection := by
    refine ⟨names, ?_⟩
    intro clock index parameters table present
    have calm := valid.statement_calm names
    change (Resolved.Statement.query (Resolved.Query.simple [Resolved.QuerySource.first witness.position]
      witness.filter witness.columns names) []).Calm at calm
    change resolveStatement _ _ _ = .ok (.query (witness.query names) [], _) at resolved
    rw [agrees clock index connection parameters, runScriptStep_query_eq resolved]
    simp [statementClock, calm.readsClock, calm.counterReads, ReadCertificate.query,
      Resolved.Query.simpleTable_checks parameters present calm, List.eraseDups_cons,
      Resolved.stableSort, Resolved.insertStable]
  apply preserves values readOnly (name := name) (by assumption) (by assumption) analyzed.1 analyzed.2.1
    ?_ place frame (by assumption) ?_
  · intro connection same
    obtain ⟨names, equal⟩ := analyzed.2.2
    apply scans analyzed.1 connection (names := names)
    rw [same, ← equal]
    assumption
  · intro connection same
    apply scans (analyzed.1.moved _) connection
    rw [same, ← moved]
    assumption

end Belay.Sqlite.KeptRead
