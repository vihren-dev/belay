import Belay.Sqlite.Model.Programs.StatementRunLaws.ForeignKeyDdlSelected
import Belay.Sqlite.Model.Tooling.Counterexamples.ForeignKeyDdlSelected
import Belay.Sqlite.Model.Programs.Scripts.InsertSelectLaws
import Belay.Sqlite.Model.Programs.Scripts.StatementDropColumn
import Belay.Sqlite.Model.Programs.Scripts.AdmittedRowsOnly
import Belay.Sqlite.Model.Programs.Scripts.KeysUniqueWrites
import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyStatement

set_option doc.verso true

namespace Belay.Sqlite.Model

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
    exact runStatement_rewrite_satisfies clock counters parameters renamed holds fun same =>
      holds.of_outline same condition
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
