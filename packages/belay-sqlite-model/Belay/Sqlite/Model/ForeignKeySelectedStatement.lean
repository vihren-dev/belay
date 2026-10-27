import Belay.Sqlite.Model.ForeignKeyStatement
import Belay.Sqlite.Model.DropColumnForeignFacts

set_option doc.verso true

/-! Parent-schema compatibility and both atoms together, through every resolved statement, for the
mapping that the catalog selects. A schema statement changes the catalog, so a fixed mapping cannot
describe the database after it; the selected mapping can. -/

namespace Belay.Sqlite.Model

/-- Sufficient conditions for a resolved statement to keep the parent schemas of a database
compatible with the selected mapping:
* CREATE, also CREATE VIEW, requires that every old declaration keeps its selected parent
  ({name}`Catalog.CreateKeepsSelection`). CREATE TABLE also requires a located parent for every
  new declaration ({name}`Catalog.CreateLocatesNewKeys`).
* ADD COLUMN requires the same for the column ({name}`Catalog.AddColumnKeepsSelection`,
  {name}`Catalog.AddColumnLocatesNewKeys`).
* DROP, with or without rules, requires that every kept declaration keeps its selected parent,
  moved ({name}`Catalog.DropKeepsSelection`).
* DROP COLUMN requires nothing, as a rename does: the run stores the new catalog only when it keeps
  the outline and the selected parents of the catalog after the drop, and no foreign key names the column.
* A rewrite of the catalog by a rename requires that every foreign key keeps its selected parent
  ({name}`Catalog.selectedParents`): the run stores the new catalog only when it keeps the outline.
* Every other form keeps the catalog and requires nothing, whatever the rows and enforcement. -/
def Resolved.Statement.ForeignKeySchemaCondition (database : Database) : Resolved.Statement → Prop
  | .createTable _ name shape => database.catalog.CreateKeepsSelection {name, entry := .table shape} ∧
      database.catalog.CreateLocatesNewKeys {name, entry := .table shape}
  | .createIndex _ name index => database.catalog.CreateKeepsSelection {name, entry := .index index}
  | .createTrigger _ name trigger => database.catalog.CreateKeepsSelection {name, entry := .trigger trigger}
  | .createView _ name view => database.catalog.CreateKeepsSelection {name, entry := .view view}
  | .addColumn target column _ => database.catalog.AddColumnKeepsSelection target column ∧
      database.catalog.AddColumnLocatesNewKeys target column
  | .drop positions _ => database.catalog.DropKeepsSelection positions
  | .begin | .commit | .rollback | .insert .. | .update .. | .upsert .. | .insertSelect .. | .delete ..
  | .prepareError _ | .query .. | .setting _ _ | .dropColumn .. => True
  | .rewrite renamed => renamed.selectedParents = database.catalog.selectedParents

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

/-- Sufficient conditions for a resolved statement to keep both atoms under the selected mapping:
* CREATE TABLE requires a located parent for every new declaration
  ({name}`Catalog.CreateLocatesNewKeys`); CREATE VIEW, CREATE INDEX and CREATE TRIGGER require nothing.
  The input atoms give the selection of every old declaration.
* ADD COLUMN requires {name}`Database.AddColumnRowsCondition` and a located parent for every
  declaration of the column ({name}`Catalog.AddColumnLocatesNewKeys`).
* DROP requires that every kept declaration keeps its selected parent, moved, and its located
  parents ({name}`Catalog.DropKeepsSelection`, {name}`Catalog.DropKeepsParents`). DROP with rules
  also requires admission, unique keys and the FK rule conditions of its implicit DELETE.
* A rewrite of the catalog by a rename requires that every foreign key keeps its selected parent
  ({name}`Catalog.selectedParents`). A DROP COLUMN requires nothing.
* Every other form requires {name}`Resolved.Statement.ForeignKeyRowsCondition`.
For a removed referenced parent, which only the row atom survives, use the individual laws. -/
def Resolved.Statement.ForeignKeyAtomsCondition (profile : Profile) (database : Database) :
    Resolved.Statement → Prop
  | .createTable _ name shape => database.catalog.CreateLocatesNewKeys {name, entry := .table shape}
  | .createIndex .. | .createTrigger .. | .createView .. => True
  | .addColumn target column refuses => database.AddColumnRowsCondition target column refuses ∧
      database.catalog.AddColumnLocatesNewKeys target column
  | .drop positions none => database.catalog.DropKeepsSelection positions ∧ database.catalog.DropKeepsParents positions
  | .drop positions (some rules) => database.ForeignKeyReady profile ∧
      rules.ForeignKeyConditions profile database.catalog ∧
      database.catalog.DropKeepsSelection positions ∧ database.catalog.DropKeepsParents positions
  | statement@(.insert ..) | statement@(.update ..) | statement@(.upsert ..) | statement@(.insertSelect ..) | statement@(.delete ..)
  | statement@.begin | statement@.commit | statement@.rollback | statement@(.prepareError _) | statement@(.rewrite _) | statement@(.dropColumn ..)
  | statement@(.query ..) | statement@(.setting _ _) => statement.ForeignKeyRowsCondition profile database

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
