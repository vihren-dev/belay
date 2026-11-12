import Belay.Sqlite.Model.Programs.Scripts.InsertSelectKeeps
import Belay.Sqlite.Model.Tooling.Counterexamples.ForeignKeySelectedStatement
import Belay.Sqlite.Model.Programs.Scripts.ScriptRunHolds

set_option doc.verso true

/-! Parent-schema compatibility and both atoms through the existing SQL and surface runs, for the
mapping that the catalog selects. They cover the schema statements. An open transaction requires
the fact on its saved snapshot too, because ROLLBACK can restore that database. -/

namespace Belay.Sqlite.Model

/-- For every profile, both atoms under the mapping that the catalog selects are kept by every
statement that meets {name}`Resolved.Statement.ForeignKeyAtomsCondition`, including the schema
statements. Proof sketch: specialize the statement theorem. -/
theorem foreignKeyAtomsSelected_statementKeeps (profile : Profile) :
    StatementKeeps (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
      database.RowReferencesHold database.catalog.foreignKeyMapping)
      (fun _ _ _ statement database => statement.ForeignKeyAtomsCondition profile database) :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ holds met =>
    runStatement_foreignKeyAtomsSelected _ clock counters parameters statement holds met)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h)

end Belay.Sqlite.Model
