import Belay.Sqlite.Model.Programs.Scripts.InsertSelectKeeps
import Belay.Sqlite.Model.Programs.StatementRunLaws.ForeignKeySelectedStatement
import Belay.Sqlite.Model.Programs.Scripts.ScriptRunHolds

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every database, parent-schema compatibility under the mapping that its catalog selects
is kept by every statement that meets {name}`Resolved.Statement.ForeignKeySchemaCondition`.
Proof sketch: specialize the statement theorem. -/
theorem parentSchemasCompatibleSelectedKeeps :
    StatementKeeps (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping)
      (fun _ _ _ statement database => statement.ForeignKeySchemaCondition database) :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ holds met =>
    runStatement_parentSchemasCompatibleSelected clock counters parameters statement holds met)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h)

end Belay.Sqlite.Model
