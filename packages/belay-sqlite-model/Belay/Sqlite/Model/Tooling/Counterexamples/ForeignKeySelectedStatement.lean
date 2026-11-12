import Belay.Sqlite.Model.Tooling.Counterexamples.ForeignKeyStatement
import Belay.Sqlite.Model.Programs.StatementRunLaws.ForeignKeySelectedStatement

set_option doc.verso true

/-! Parent-schema compatibility and both atoms together, through every resolved statement, for the
mapping that the catalog selects. A schema statement changes the catalog, so a fixed mapping cannot
describe the database after it; the selected mapping can. -/

namespace Belay.Sqlite.Model

/-- For every profile, clock, counters, parameters, statement and database with both atoms under
the selected mapping: if the statement meets {name}`Resolved.Statement.ForeignKeyAtomsCondition`,
every success and partial FAIL has both atoms under the mapping that its own catalog selects.
Other error carriers require nothing. Proof sketch: a schema statement uses its combined law;
every other form uses the row law and the schema law above. -/
theorem runStatement_foreignKeyAtomsSelected (profile : Profile) (clock : Int) (counters : Counters)
    (parameters : List Value) (statement : Resolved.Statement) {database : Database}
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
      database.RowReferencesHold database.catalog.foreignKeyMapping)
    (condition : statement.ForeignKeyAtomsCondition profile database) :
    (runStatement clock counters parameters statement database).effect.Satisfies
      (fun after => after.ParentSchemasCompatible after.catalog.foreignKeyMapping ∧
        after.RowReferencesHold after.catalog.foreignKeyMapping) := by
  have written (rows : statement.ForeignKeyRowsCondition profile database) (schema : statement.ForeignKeySchemaCondition database) :
      (runStatement clock counters parameters statement database).effect.Satisfies
        (fun after => after.ParentSchemasCompatible after.catalog.foreignKeyMapping ∧
          after.RowReferencesHold after.catalog.foreignKeyMapping) := fun after kept =>
    ⟨runStatement_parentSchemasCompatibleSelected clock counters parameters statement holds.1 schema after kept,
      runStatement_rowReferences clock counters parameters statement holds.2 rows after kept⟩
  cases statement with
  | createTable _ name shape =>
    exact runStatement_create_foreignKeyAtoms clock counters parameters _ {name, entry := .table shape} rfl holds
      condition
  | createIndex _ name index =>
    exact runStatement_create_foreignKeyAtoms clock counters parameters _ {name, entry := .index index} rfl holds
      (fun _ entry => nomatch entry)
  | createTrigger _ name trigger =>
    exact runStatement_create_foreignKeyAtoms clock counters parameters _ {name, entry := .trigger trigger} rfl holds
      (fun _ entry => nomatch entry)
  | createView _ name view =>
    exact runStatement_create_foreignKeyAtoms clock counters parameters _ {name, entry := .view view} rfl holds
      (fun _ entry => nomatch entry)
  | addColumn target column refuses =>
    exact runStatement_addColumn_foreignKeyAtoms clock counters parameters target column refuses holds
      condition.1.wide condition.1.declared condition.1.below condition.2 condition.1.newKeys
  | drop positions rules =>
    cases rules with
    | none =>
      exact runStatement_drop_foreignKeyAtoms clock counters parameters positions holds
        (fun child table found kept key declared => condition.1 child table.shape (Database.tableAt_of_table found) kept key declared)
        (fun child table found kept key declared => condition.2 child table.shape (Database.tableAt_of_table found) kept key declared)
    | some rules =>
      obtain ⟨ready, conditions, selection, parents⟩ := condition
      exact runStatement_drop_enforced_foreignKeyAtoms rules clock counters parameters positions ready holds conditions
        selection parents
  | dropColumn position index stored =>
    exact runStatement_dropColumn_satisfies clock counters parameters position index stored holds fun runs =>
      ⟨holds.1.dropColumn runs, holds.2.dropColumn runs⟩
  | rewrite renamed =>
    exact runStatement_rewrite_satisfies clock counters parameters renamed holds fun same =>
      ⟨holds.1.of_outline same condition, holds.2.of_outline same condition⟩
  | begin | commit | rollback | insert | update | upsert | insertSelect | delete | prepareError | query | setting =>
    exact written condition trivial

end Belay.Sqlite.Model
