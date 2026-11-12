import Belay.Sqlite.Model.Programs.Scripts.AdmittedRowsOnly
import Belay.Sqlite.Model.Programs.Scripts.RowLocalWrites
import Belay.Sqlite.Model.Programs.Scripts.InsertSelectLaws
import Belay.Sqlite.Model.Schema.Columns.ForeignKeySchemaWrites

set_option doc.verso true

/-! Parent-schema compatibility through statements that retain the catalog. Foreign-key
enforcement and stored rows are unrestricted: this atom reads declarations and parent selection. -/

namespace Belay.Sqlite.Model

/-- For every mapping, clock, counters, parameters and input with compatible parent schemas,
a statement satisfying {name}`Resolved.Statement.KeepsParentSchema` preserves compatibility
on success and partial FAIL. Other error carriers impose no condition; SQL retains the input
or restores its snapshot. Proof sketch: plain writes retain the catalog, row-engine writes
use {name}`rowsKeys_parentSchemasCompatible`, and the remaining forms keep the database. -/
theorem runStatement_parentSchemasCompatible (mapping : ForeignKeyMapping) (clock : Int)
    (counters : Counters) (parameters : List Value) (statement : Resolved.Statement) {database : Database}
    (holds : database.ParentSchemasCompatible mapping) (met : statement.KeepsParentSchema) :
    (runStatement clock counters parameters statement database).effect.Satisfies
      (Database.ParentSchemasCompatible mapping) := by
  cases statement with
  | createTable | createView | createIndex | createTrigger | addColumn | rewrite | dropColumn | drop => exact False.elim met
  | begin | commit | rollback | prepareError | query | setting =>
    apply Effect.satisfies_of_database holds
    apply runStatement_keeps_database
    simp
  | insert target rows returning subqueries rules =>
    cases rules with
    | none =>
      exact Effect.satisfies_of_effectDatabase (holds.catalog_eq
        ((runStatement_plain_rowsOnly clock counters parameters _ database target (.inl ⟨rows, returning, subqueries, rfl⟩)).catalog))
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database holds rfl
      · exact rowsKeys_parentSchemasCompatible mapping rules clock target _ holds _ _
  | update target assignments filter returning subqueries rules =>
    cases rules with
    | none =>
      exact Effect.satisfies_of_effectDatabase (holds.catalog_eq
        ((runStatement_plain_rowsOnly clock counters parameters _ database target
          (.inr (.inl ⟨assignments, filter, returning, subqueries, rfl⟩))).catalog))
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database holds rfl
      · exact rowsKeys_parentSchemasCompatible mapping rules _ target _ holds _ _
  | upsert target rows clauses returning algorithm subqueries rules =>
    cases rules with
    | none =>
      exact Effect.satisfies_of_effectDatabase (holds.catalog_eq
        ((runStatement_plain_rowsOnly clock counters parameters _ database target
          (.inr (.inr (.inl ⟨rows, clauses, returning, algorithm, subqueries, rfl⟩)))).catalog))
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database holds rfl
      · exact rowsKeys_parentSchemasCompatible mapping rules clock target _ holds _ _
  | insertSelect target cells query clauses returning algorithm subqueries rules =>
    cases rules with
    | none =>
      exact runStatement_insertSelect_none_satisfies clock counters parameters target cells query clauses returning algorithm subqueries holds
        fun literals => Effect.satisfies_of_effectDatabase (holds.catalog_eq
          ((runStatement_plain_rowsOnly clock counters parameters _ database target
            (.inr (.inr (.inl ⟨literals, clauses, returning, algorithm, subqueries, rfl⟩)))).catalog))
    | some rules =>
      exact runStatement_insertSelect_some_satisfies clock counters parameters target cells query clauses returning algorithm subqueries rules holds
        fun _ _ _ plain conflict => rowsKeys_parentSchemasCompatible mapping rules clock target _ holds plain conflict
  | delete target filter returning subqueries rules =>
    cases rules with
    | none =>
      exact Effect.satisfies_of_effectDatabase (holds.catalog_eq
        ((runStatement_plain_rowsOnly clock counters parameters _ database target
          (.inr (.inr (.inr ⟨filter, returning, subqueries, rfl⟩)))).catalog))
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database holds rfl
      · exact rowsKeys_parentSchemasCompatible mapping rules _ target _ holds _ _

end Belay.Sqlite.Model
