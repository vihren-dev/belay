import Belay.Sqlite.Model.InsertSelectKeeps
import Belay.Sqlite.Model.ForeignKeySchemaWrites
import Belay.Sqlite.Model.ScriptRunHolds

set_option doc.verso true

/-! Parent-schema compatibility through the existing SQL and surface runs. An open transaction
requires the fact on its saved snapshot too, because ROLLBACK can restore that database. -/

namespace Belay.Sqlite.Model

/-- For every supplied mapping, each statement satisfying
{name}`Resolved.Statement.KeepsParentSchema` preserves compatible parent schemas. The condition
does not inspect stored rows. Proof sketch: specialize the statement theorem. -/
theorem parentSchemasCompatibleKeeps (mapping : ForeignKeyMapping) :
    StatementKeeps (Database.ParentSchemasCompatible mapping)
      (fun statement _ => statement.KeepsParentSchema) :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ holds met =>
    runStatement_parentSchemasCompatible mapping clock counters parameters statement holds met)
    (fun _ _ _ _ _ _ _ _ _ h => h)

end Belay.Sqlite.Model
