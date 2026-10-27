import Belay.Sqlite.Model.ForeignKeyPlainFrame
import Belay.Sqlite.Model.ForeignKeyWriteConditions
import Belay.Sqlite.Model.ForeignKeyDdlSelected
import Belay.Sqlite.Model.InsertSelectLaws
import Belay.Sqlite.Model.StatementRewrite
import Belay.Sqlite.Model.StatementDropColumn
import Belay.Sqlite.Model.DropColumnForeignFacts
import Belay.Sqlite.Model.OutlineSelectedParentLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Sufficient conditions for selected row-reference preservation by a resolved statement:
* INSERT, UPSERT and DELETE with rules require admission, unique keys and FK rule conditions.
* UPDATE with rules also requires structural assignment conditions.
* Those four plain forms without rules require a target outside every FK child/parent read.
* Queries, settings, preparation errors and transaction controls require nothing here.
* CREATE, also CREATE VIEW, requires that every old declaration keeps its selected parent
  ({name}`Catalog.CreateKeepsSelection`). New declarations have no rows to check. A view has no
  rows and no declarations.
* A rewrite of the catalog by a rename requires nothing: the run stores the new catalog only when
  it keeps the outline and the selected parents, and the rows then find their parents again.
* DROP COLUMN requires nothing: the run drops the cells only when the stored catalog has the outline and the
  selected parents of the catalog after the drop, and the dropped column is none that a foreign key names
  ({name}`Catalog.droppable`).
* ADD COLUMN requires {name}`Database.AddColumnRowsCondition`.
* DROP without rules requires that every kept declaration keeps its selected parent, moved, and its
  located parents ({name}`Catalog.DropKeepsSelection`, {name}`Catalog.DropKeepsParents`).
* DROP with rules requires admission, unique keys, the FK rule conditions of its implicit DELETE
  and {name}`Database.EnforcedDropFrames`.
Rule-based UPSERT DO UPDATE still has its current undescribed result; this condition does not
promise successful execution of that branch. -/
def Resolved.Statement.ForeignKeyRowsCondition (profile : Profile) (database : Database) : Resolved.Statement → Prop
  | .insert target _ _ _ rules | .upsert target _ _ _ _ _ rules | .insertSelect target _ _ _ _ _ _ rules | .delete target _ _ _ rules =>
      match rules with
      | none => database.catalog.ForeignKeyOutside target
      | some rules => database.ForeignKeyReady profile ∧ rules.ForeignKeyConditions profile database.catalog
  | .update target assignments _ _ _ rules =>
      match rules with
      | none => database.catalog.ForeignKeyOutside target
      | some rules => database.ForeignKeyReady profile ∧ rules.ForeignKeyConditions profile database.catalog ∧
          ForeignKeyAssignmentConditions database.catalog target assignments
  | .begin | .commit | .rollback | .query .. | .prepareError _ | .setting .. | .rewrite _ | .dropColumn .. => True
  | .createTable _ name shape => database.catalog.CreateKeepsSelection {name, entry := .table shape}
  | .createIndex _ name index => database.catalog.CreateKeepsSelection {name, entry := .index index}
  | .createTrigger _ name trigger => database.catalog.CreateKeepsSelection {name, entry := .trigger trigger}
  | .createView _ name view => database.catalog.CreateKeepsSelection {name, entry := .view view}
  | .addColumn target column refuses => database.AddColumnRowsCondition target column refuses
  | .drop positions none => database.catalog.DropKeepsSelection positions ∧ database.catalog.DropKeepsParents positions
  | .drop positions (some rules) => database.ForeignKeyReady profile ∧
      rules.ForeignKeyConditions profile database.catalog ∧ database.EnforcedDropFrames rules positions

/-- For every clock, counters, parameters and input with selected row references, a
statement meeting its FK conditions retains that row fact on success and partial FAIL.
Other error carriers impose nothing here; SQL restores the input or saved snapshot.
Proof sketch: plain writes use the outside-footprint frame. Enforced writes use the actual
row-engine theorem, and UPDATE derives complete coverage from its assignment constructor.
Nonwriting forms keep the input database; the schema forms use their selected-mapping laws. -/
theorem runStatement_rowReferences {profile : Profile} (clock : Int) (counters : Counters) (parameters : List Value)
    (statement : Resolved.Statement) {database : Database}
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (condition : statement.ForeignKeyRowsCondition profile database) :
    (runStatement clock counters parameters statement database).effect.Satisfies
      (fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  cases statement with
  | createTable _ name shape =>
    exact runStatement_create_rowReferencesSelected clock counters parameters _ {name, entry := .table shape} rfl holds condition
  | createIndex _ name index =>
    exact runStatement_create_rowReferencesSelected clock counters parameters _ {name, entry := .index index} rfl holds condition
  | createTrigger _ name trigger =>
    exact runStatement_create_rowReferencesSelected clock counters parameters _ {name, entry := .trigger trigger} rfl holds condition
  | createView _ name view =>
    exact runStatement_create_rowReferencesSelected clock counters parameters _ {name, entry := .view view} rfl holds condition
  | addColumn target column refuses =>
    exact runStatement_addColumn_rowReferencesSelected clock counters parameters target column refuses holds condition
  | drop positions rules =>
    cases rules with
    | none => exact runStatement_drop_rowReferencesSelected clock counters parameters positions holds condition.1 condition.2
    | some rules =>
      obtain ⟨ready, conditions, frames⟩ := condition
      exact runStatement_drop_enforced_rowReferences rules clock counters parameters positions ready holds conditions
        (frames.1 clock) frames.2
  | dropColumn position index stored =>
    exact runStatement_dropColumn_satisfies clock counters parameters position index stored holds fun runs =>
      holds.dropColumn runs
  | rewrite renamed =>
    exact runStatement_rewrite_satisfies clock counters parameters renamed holds fun same parents =>
      holds.of_outline same parents
  | begin | commit | rollback | prepareError | query | setting =>
    apply Effect.satisfies_of_database (property := fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) holds
    apply runStatement_keeps_database
    simp
  | insert target rows returning subqueries rules =>
    cases rules with
    | none =>
      apply Effect.satisfies_of_effectDatabase
      exact holds.rowsOnlyAt condition
        (runStatement_plain_rowsOnly clock counters parameters _ database target (.inl ⟨rows, returning, subqueries, rfl⟩))
    | some value =>
      obtain ⟨ready, facts⟩ := condition
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database (property := fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) holds rfl
      · exact rowsKeys_rowReferences value clock target _ ready holds facts.enforced facts.comparisons
          facts.programs facts.actions facts.before (by trivial) _ _
  | upsert target rows clauses returning algorithm subqueries rules =>
    cases rules with
    | none =>
      apply Effect.satisfies_of_effectDatabase
      exact holds.rowsOnlyAt condition
        (runStatement_plain_rowsOnly clock counters parameters _ database target
          (.inr (.inr (.inl ⟨rows, clauses, returning, algorithm, subqueries, rfl⟩))))
    | some value =>
      obtain ⟨ready, facts⟩ := condition
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database (property := fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) holds rfl
      · exact rowsKeys_rowReferences value clock target _ ready holds facts.enforced facts.comparisons
          facts.programs facts.actions facts.before (by trivial) _ _
  | insertSelect target cells query clauses returning algorithm subqueries rules =>
    cases rules with
    | none =>
      exact runStatement_insertSelect_none_satisfies clock counters parameters target cells query clauses returning algorithm
        subqueries holds fun literals => by
          apply Effect.satisfies_of_effectDatabase
          exact holds.rowsOnlyAt condition
            (runStatement_plain_rowsOnly clock counters parameters _ database target
              (.inr (.inr (.inl ⟨literals, clauses, returning, algorithm, subqueries, rfl⟩))))
    | some value =>
      obtain ⟨ready, facts⟩ := condition
      exact runStatement_insertSelect_some_satisfies clock counters parameters target cells query clauses returning algorithm
        subqueries value holds fun _ _ _ plain conflict => rowsKeys_rowReferences value clock target _ ready holds
          facts.enforced facts.comparisons facts.programs facts.actions facts.before (by trivial) plain conflict
  | delete target filter returning subqueries rules =>
    cases rules with
    | none =>
      apply Effect.satisfies_of_effectDatabase
      exact holds.rowsOnlyAt condition
        (runStatement_plain_rowsOnly clock counters parameters _ database target
          (.inr (.inr (.inr ⟨filter, returning, subqueries, rfl⟩))))
    | some value =>
      obtain ⟨ready, facts⟩ := condition
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database (property := fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) holds rfl
      · exact rowsKeys_rowReferences value _ target _ ready holds facts.enforced facts.comparisons
          facts.programs facts.actions facts.before (by trivial) _ _
  | update target assignments filter returning subqueries rules =>
    cases rules with
    | none =>
      apply Effect.satisfies_of_effectDatabase
      exact holds.rowsOnlyAt condition
        (runStatement_plain_rowsOnly clock counters parameters _ database target
          (.inr (.inl ⟨assignments, filter, returning, subqueries, rfl⟩)))
    | some value =>
      obtain ⟨ready, facts, changes⟩ := condition
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database (property := fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) holds rfl
      · rename_i table found
        exact rowsKeys_rowReferences value _ target _ ready holds facts.enforced facts.comparisons
          facts.programs facts.actions facts.before
          (by exact changes.work table.shape (KeyState.table_shape (state := {rows := database.rows}) found) _ (·.values)) _ _

end Belay.Sqlite.Model
