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

/-- For every mapping, starting position, resolved script and state, if both the current
database and any saved snapshot have compatible parent schemas, and every reached statement
keeps the catalog, then all databases retained by the SQL outcome have compatible parent
schemas. This covers success, errors, partial FAIL and rollback. A halted run requires no
condition on its unreached suffix. Proof sketch: apply {name}`runSqlFrom_holds` with the schema
statement theorem; its state invariant includes the saved snapshot. -/
theorem runSqlFrom_parentSchemasCompatible (mapping : ForeignKeyMapping) (position : Nat)
    (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds (Database.ParentSchemasCompatible mapping))
    (conditions : RunConditionsWith (fun statement _ => statement.KeepsParentSchema) position script state) :
    (runSqlFrom position script state).Holds (Database.ParentSchemasCompatible mapping) :=
  runSqlFrom_holds (parentSchemasCompatibleKeeps mapping) position script holds conditions

/-- For every mapping, resolved script and database with compatible parent schemas, a fresh
SQL run retains compatibility in all outcome databases when every reached statement keeps
the catalog. The fresh run has no snapshot entry requirement. Proof sketch: specialize
{name}`runSql_holds` with the schema statement theorem. -/
theorem runSql_parentSchemasCompatible (mapping : ForeignKeyMapping)
    (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : database.ParentSchemasCompatible mapping)
    (conditions : RunConditionsWith (fun statement _ => statement.KeepsParentSchema) 0 script { database }) :
    (runSql script database).Holds (Database.ParentSchemasCompatible mapping) :=
  runSql_holds (parentSchemasCompatibleKeeps mapping) script holds conditions

/-- For every mapping, resolution context, clock, index, connection and surface script, if
the connection's database and saved snapshot have compatible parent schemas, and each reached
resolved statement keeps the catalog, then in every complete execution of the script
({name}`runScriptAllFrom`) the final connection's database and snapshot have compatible parent
schemas. Failed resolution and halted suffixes impose no extra condition.
Proof sketch: apply {name}`runScriptAllFrom_holds` with the same schema statement theorem. -/
theorem runScriptAllFrom_parentSchemasCompatible (mapping : ForeignKeyMapping) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) {connection : Connection}
    (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds (Database.ParentSchemasCompatible mapping))
    (conditions : ScriptConditionsWith (fun statement _ => statement.KeepsParentSchema)
      context clock index connection script) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (Database.ParentSchemasCompatible mapping) :=
  runScriptAllFrom_holds (parentSchemasCompatibleKeeps mapping) context clock index script holds conditions

end Belay.Sqlite.Model
