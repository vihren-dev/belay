import Belay.Sqlite.Model.ForeignKeySelectedStatement
import Belay.Sqlite.Model.ScriptRunHolds

set_option doc.verso true

/-! Parent-schema compatibility and both atoms through the existing SQL and surface runs, for the
mapping that the catalog selects. They cover the schema statements. An open transaction requires
the fact on its saved snapshot too, because ROLLBACK can restore that database. -/

namespace Belay.Sqlite.Model

/-- For every database, parent-schema compatibility under the mapping that its catalog selects
is kept by every statement that meets {name}`Resolved.Statement.ForeignKeySchemaCondition`.
Proof sketch: specialize the statement theorem. -/
theorem parentSchemasCompatibleSelectedKeeps :
    StatementKeeps (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping)
      (fun statement database => statement.ForeignKeySchemaCondition database) :=
  fun clock counters parameters statement _ holds met =>
    runStatement_parentSchemasCompatibleSelected clock counters parameters statement holds met

/-- For every resolved script, starting position and state, if the current database and any saved
snapshot have compatible parent schemas under their selected mappings, and every reached
statement meets its schema condition, every database that the outcome retains has them. This covers
success, errors, partial FAIL and rollback. A halted run requires nothing of its unreached suffix.
Proof sketch: apply {name}`runSqlFrom_holds` with the statement theorem. -/
theorem runSqlFrom_parentSchemasCompatibleSelected (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState}
    (holds : state.Holds (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping))
    (conditions : RunConditionsWith (fun statement database => statement.ForeignKeySchemaCondition database)
      position script state) :
    (runSqlFrom position script state).Holds
      (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping) :=
  runSqlFrom_holds parentSchemasCompatibleSelectedKeeps position script holds conditions

/-- For every fresh resolved script and database with compatible parent schemas under its selected
mapping, every database that the outcome retains has them when every reached statement meets its
schema condition. A fresh run has no saved snapshot. Proof sketch: specialize
{name}`runSql_holds` with the statement theorem. -/
theorem runSql_parentSchemasCompatibleSelected (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping)
    (conditions : RunConditionsWith (fun statement database => statement.ForeignKeySchemaCondition database)
      0 script {database}) :
    (runSql script database).Holds (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping) :=
  runSql_holds parentSchemasCompatibleSelectedKeeps script holds conditions

/-- For every resolution context, clock, index, connection and surface script: if the database and
the saved snapshot of the connection have compatible parent schemas under their selected mappings,
and every reached resolved statement meets its schema condition, then in every complete
execution of the script ({name}`runScriptAllFrom`) the final connection has them in both. Failed resolution and halted suffixes add no condition. Proof sketch: apply
{name}`runScriptAllFrom_holds` with the statement theorem. -/
theorem runScriptAllFrom_parentSchemasCompatibleSelected (context : ResolveContext) (clock : Option Clock)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds
      (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping))
    (conditions : ScriptConditionsWith (fun statement database => statement.ForeignKeySchemaCondition database)
      context clock index connection script) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping) :=
  runScriptAllFrom_holds parentSchemasCompatibleSelectedKeeps context clock index script holds conditions

/-- For every profile, both atoms under the mapping that the catalog selects are kept by every
statement that meets {name}`Resolved.Statement.ForeignKeyAtomsCondition`, including the schema
statements. Proof sketch: specialize the statement theorem. -/
theorem foreignKeyAtomsSelected_statementKeeps (profile : Profile) :
    StatementKeeps (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
      database.RowReferencesHold database.catalog.foreignKeyMapping)
      (fun statement database => statement.ForeignKeyAtomsCondition profile database) :=
  fun clock counters parameters statement _ holds met =>
    runStatement_foreignKeyAtomsSelected _ clock counters parameters statement holds met

/-- For every resolved script, starting position and state, if both atoms hold under the selected
mappings on the current database and any saved snapshot, and every reached statement meets its
atoms condition, both hold on every database that the outcome retains, including rollback and
pending snapshots. Proof sketch: apply {name}`runSqlFrom_holds` with the statement theorem. -/
theorem runSqlFrom_foreignKeyAtomsSelected (profile : Profile) (position : Nat)
    (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
      database.RowReferencesHold database.catalog.foreignKeyMapping))
    (conditions : RunConditionsWith (fun statement database => statement.ForeignKeyAtomsCondition profile database)
      position script state) :
    (runSqlFrom position script state).Holds
      (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
        database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  runSqlFrom_holds (foreignKeyAtomsSelected_statementKeeps profile) position script holds conditions

/-- For every fresh resolved script and database with both atoms under the selected mapping, both
atoms hold on every database that the outcome retains when every reached statement meets its atoms
condition. A fresh run has no saved snapshot. Proof sketch: specialize {name}`runSql_holds` with the
statement theorem. -/
theorem runSql_foreignKeyAtomsSelected (profile : Profile) (script : List (Resolved.Statement × List Value))
    {database : Database}
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
      database.RowReferencesHold database.catalog.foreignKeyMapping)
    (conditions : RunConditionsWith (fun statement database => statement.ForeignKeyAtomsCondition profile database)
      0 script {database}) :
    (runSql script database).Holds
      (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
        database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  runSql_holds (foreignKeyAtomsSelected_statementKeeps profile) script holds conditions

/-- For every resolution context, clock, index, connection and surface script: if both atoms hold
under the selected mappings on the database and the saved snapshot of the connection, and every
reached resolved statement meets its atoms condition, then in every complete execution of the
script ({name}`runScriptAllFrom`) both hold in the final connection's database and snapshot. Failed resolution and halted suffixes add no condition. Proof sketch: apply
{name}`runScriptAllFrom_holds` with the statement theorem. -/
theorem runScriptAllFrom_foreignKeyAtomsSelected (profile : Profile) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds (fun database =>
      database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
        database.RowReferencesHold database.catalog.foreignKeyMapping))
    (conditions : ScriptConditionsWith (fun statement database => statement.ForeignKeyAtomsCondition profile database)
      context clock index connection script) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
        database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  runScriptAllFrom_holds (foreignKeyAtomsSelected_statementKeeps profile) context clock index script holds conditions

end Belay.Sqlite.Model
