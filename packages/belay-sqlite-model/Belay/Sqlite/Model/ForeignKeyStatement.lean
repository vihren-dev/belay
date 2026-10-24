import Belay.Sqlite.Model.ForeignKeyPlainFrame
import Belay.Sqlite.Model.ForeignKeyWriteConditions
import Belay.Sqlite.Model.ForeignKeySchemaWrites

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Sufficient conditions for selected row-reference preservation by a resolved statement:
* INSERT, UPSERT and DELETE with rules require admission, unique keys and FK rule conditions.
* UPDATE with rules also requires structural assignment conditions.
* Those four plain forms without rules require a target outside every FK child/parent read.
* Queries, settings, preparation errors and transaction controls require nothing here.
* CREATE, ADD COLUMN and DROP do not meet this condition; their mapping changes need
  separate transport laws. Rule-based UPSERT DO UPDATE still has its current undescribed
  result; this condition does not promise successful execution of that branch. -/
def Resolved.Statement.ForeignKeyRowsCondition (profile : Profile) (database : Database) : Resolved.Statement → Prop
  | .insert target _ _ _ rules | .upsert target _ _ _ _ _ rules | .delete target _ _ _ rules =>
      match rules with
      | none => database.catalog.ForeignKeyOutside target
      | some rules => database.ForeignKeyReady profile ∧ rules.ForeignKeyConditions profile database.catalog
  | .update target assignments _ _ _ rules =>
      match rules with
      | none => database.catalog.ForeignKeyOutside target
      | some rules => database.ForeignKeyReady profile ∧ rules.ForeignKeyConditions profile database.catalog ∧
          ForeignKeyAssignmentConditions database.catalog target assignments
  | .begin | .commit | .rollback | .query .. | .prepareError _ | .setting .. => True
  | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .drop .. => False

/-- For every clock, counters, parameters and input with selected row references, a
statement meeting its FK conditions retains that row fact on success and partial FAIL.
Other error carriers impose nothing here; SQL restores the input or saved snapshot.
Proof sketch: plain writes use the outside-footprint frame. Enforced writes use the actual
row-engine theorem, and UPDATE derives complete coverage from its assignment constructor.
Nonwriting forms keep the input database; catalog-changing forms are outside this law. -/
theorem runStatement_rowReferences {profile : Profile} (clock : Int) (counters : Counters) (parameters : List Value)
    (statement : Resolved.Statement) {database : Database}
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (condition : statement.ForeignKeyRowsCondition profile database) :
    (runStatement clock counters parameters statement database).effect.Satisfies
      (fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  cases statement with
  | createTable | createIndex | createTrigger | addColumn | drop => exact False.elim condition
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

/-- Every statement meeting the row-preservation condition retains its catalog and so
meets the schema-preservation condition. Proof sketch: inspect its form; catalog-changing
forms contradict the supplied row condition. -/
theorem Resolved.Statement.ForeignKeyRowsCondition.keepsParentSchema {profile : Profile} {database : Database}
    {statement : Resolved.Statement} (condition : statement.ForeignKeyRowsCondition profile database) :
    statement.KeepsParentSchema := by
  cases statement <;> first | trivial | exact False.elim condition

end Belay.Sqlite.Model
