import Belay.Sqlite.Model.Programs.StatementRunLaws.ForeignKeyDdlSelected
import Belay.Sqlite.Model.Programs.StatementRunLaws.ForeignKeySchemaWrites
import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeySelectedStatement

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every clock, counters, parameters, statement and database with compatible parent schemas
under the selected mapping: if the statement meets {name}`Resolved.Statement.ForeignKeySchemaCondition`,
every success and partial FAIL has compatible parent schemas under the mapping that its own catalog
selects. Other error carriers require nothing; SQL restores the input or its snapshot. Stored rows
and enforcement are unrestricted. Proof sketch: a schema statement uses its separate law; every other
form retains the catalog, so its law for a fixed mapping applies and the fixed mapping is the
selected one ({name}`Database.ParentSchemasCompatible.selected`). -/
theorem runStatement_parentSchemasCompatibleSelected (clock : Int) (counters : Counters)
    (parameters : List Value) (statement : Resolved.Statement) {database : Database}
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping)
    (condition : statement.ForeignKeySchemaCondition database) :
    (runStatement clock counters parameters statement database).effect.Satisfies
      (fun after => after.ParentSchemasCompatible after.catalog.foreignKeyMapping) := by
  have retained (met : statement.KeepsParentSchema) :
      (runStatement clock counters parameters statement database).effect.Satisfies
        (fun after => after.ParentSchemasCompatible after.catalog.foreignKeyMapping) :=
    fun after kept => (runStatement_parentSchemasCompatible _ clock counters parameters statement holds met after kept).selected
  cases statement with
  | createTable _ name shape =>
    exact runStatement_create_parentSchemasCompatibleSelected clock counters parameters _ {name, entry := .table shape}
      rfl holds condition.1 condition.2
  | createIndex _ name index =>
    exact runStatement_create_parentSchemasCompatibleSelected clock counters parameters _ {name, entry := .index index}
      rfl holds condition (fun _ entry => nomatch entry)
  | createTrigger _ name trigger =>
    exact runStatement_create_parentSchemasCompatibleSelected clock counters parameters _
      {name, entry := .trigger trigger} rfl holds condition (fun _ entry => nomatch entry)
  | createView _ name view =>
    exact runStatement_create_parentSchemasCompatibleSelected clock counters parameters _
      {name, entry := .view view} rfl holds condition (fun _ entry => nomatch entry)
  | addColumn target column refuses =>
    exact runStatement_addColumn_parentSchemasCompatibleSelected clock counters parameters target column refuses
      holds condition.1 condition.2
  | drop positions rules =>
    exact runStatement_drop_parentSchemasCompatibleSelected clock counters parameters positions rules holds condition
  | dropColumn position index stored =>
    exact runStatement_dropColumn_satisfies clock counters parameters position index stored holds fun runs =>
      holds.dropColumn runs
  | rewrite renamed =>
    exact runStatement_rewrite_satisfies clock counters parameters renamed holds fun same =>
      holds.of_outline same condition
  | begin | commit | rollback | insert | update | upsert | insertSelect | delete | prepareError | query | setting => exact retained trivial

end Belay.Sqlite.Model
