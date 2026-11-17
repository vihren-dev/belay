import Belay.Sqlite.Programs.Claims.SendSchemaPath
import Belay.Sqlite.Programs.Reasoning.ReadCertificatePreservation
import Belay.Sqlite.Programs.Reasoning.MigrationPatternFresh
import Belay.Sqlite.Schema.Dispatch.ReadAnalysis

set_option doc.verso true

/-! Apply a single-table read certificate to every successful branch of a migration. -/

namespace Belay.Sqlite
open Model

/-- If the catalog of a schema finds a table at a position, every database with that
catalog finds a table of the same definition there under the same name. Its rows are
the rows of that database. Proof sketch: the shared catalog gives the lookup and the
database supplies the rows at that position. -/
theorem Database.tableNamed_of_hasCatalog {db schema : Database} (same : db.HasCatalog schema)
    {name : Identifier} {position : Nat} {shape : CatalogTable}
    (lookup : schema.raw.catalog.findTable name = some (position, shape)) :
    ∃ table, db.raw.tableNamed name = some (position, table) ∧ table.shape = shape := by
  rw [← same] at lookup
  exact ⟨_, by rw [Model.Database.tableNamed_of_findTable lookup,
    Model.Database.table_of_findTable _ _ _ _ lookup]; rfl, rfl⟩

/-- Every row scanned from a table in a valid database has one cell for each column
of its definition. Proof sketch: the scan permutes stored rows, and validity gives
the width of every stored row. -/
theorem Database.sourceRow_width (db : Database) {position : Nat} {table : Table}
    (present : db.raw.table position = some table) {row : List Value} (scanned : row ∈ Resolved.sourceRows table) :
    row.length = table.shape.columns.length := by
  obtain ⟨stored, member, rfl⟩ := List.mem_map.mp scanned
  exact db.valid.admitted.rowsWide position table present stored (table.scanRows_perm.mem_iff.mp member)

namespace KeptRead

/-- For every migration that resolves on a schema, suppose a named table has a certified
read using its column count, the table check carries it to a final position found by the
same name, and the read resolves there to the moved certificate. Then the migration
preserves that read with any given parameter values on every database with the schema.
The success domain of {name}`Migration.QueryPreserves` imposes no obligation when the
migration fails. Proof sketch: the schema and table path laws apply to every successful
branch. Equal table rows and the width of valid rows discharge the read certificate. -/
theorem preserves {schema : Database} {migration : Script} {statement : Syntax.Statement} (values : List Value)
    {name : Identifier} {position destination : Nat} {shape finalShape : CatalogTable}
    {path : List Resolved.Statement} {final readState afterState : ResolveState} {read : Resolved.Statement}
    {certificate : ReadCertificate} {names : List String}
    (readOnly : (⟨[(statement, values)]⟩ : Script).isQuery = true)
    (checked : resolveFrom runContext 0 schema.raw.connection.resolveState (migration.statements.map Prod.fst) =
      .ok (path, final))
    (lookup : schema.raw.catalog.findTable name = some (position, shape))
    (resolved : resolveStatement runContext schema.raw.connection.resolveState statement = .ok (read, readState))
    (certified : ReadAnalysis.analyze shape.columns.length read = .certified certificate)
    (place : certificate.position = position)
    (frame : schema.raw.connection.resolveState.tablePosition path migration.statements.length position =
      some destination)
    (lookupAfter : final.catalog.findTable name = some (destination, finalShape))
    (resolvedAfter : resolveStatement runContext final statement =
      .ok ((certificate.moved destination).statement names, afterState)) :
    Migration.QueryPreserves (send migration) ⟨[(statement, values)]⟩ (·.HasCatalog schema) readOnly := by
  intro db pre env complete
  obtain ⟨table, named, shapeEq⟩ := Database.tableNamed_of_hasCatalog pre lookup
  have present := (Model.Database.tableNamed_some named).2
  have start : (db.raw.connection env.counters).resolveState = schema.raw.connection.resolveState := by
    simp [Database.Raw.connection, Connection.resolveState, Database.HasCatalog] at pre ⊢
    exact pre
  obtain ⟨validRead, width, _⟩ := ReadAnalysis.analyze_sound certified
  exact ReadCertificate.preservesAt (send migration) validRead statement values (fun _ => True)
    (ExecutionContext.initial db env) fun domain branch ran => by
      have ok := (Sql.succeedsFrom_iff_branches _ _ _ _).mp domain.2 branch ran
      have valid : (db.raw.connection env.counters).state.Holds (Database.Valid Profile.pinned) :=
        ⟨db.valid, fun _ shown => by simp [Database.Raw.connection] at shown⟩
      have ended := sendStatements_branch_resolveState checked start valid ran ok.1 ok.2
      have tableAt := sendStatements_branch_keepsTable checked frame start valid present ran ok.1 ok.2
      have catalog : branch.connection.state.database.catalog = final.catalog := congrArg ResolveState.catalog ended
      rw [← catalog] at lookupAfter
      refine ⟨ReadAnalysis.resolvesOriginal (connection := db.raw.connection env.counters) (by rw [start]; exact resolved) certified,
        name, destination, table, table, fun _ => [], ?_, ?_, ⟨names, afterState, ?_⟩, by simp, ?_⟩
      · rw [place]; exact named
      · rw [Model.Database.tableNamed_of_findTable lookupAfter, tableAt]; rfl
      · rw [ended]; exact resolvedAfter
      · intro row member
        simp only [width, ← shapeEq, db.sourceRow_width present member, Nat.le_refl]

end KeptRead
end Belay.Sqlite
