import Belay.Sqlite.Model.ForeignKeySchemaFrame
import Belay.Sqlite.Model.AdmittedRowsOnly
import Belay.Sqlite.Model.RowLocalWrites
import Belay.Sqlite.Model.InsertSelectLaws

set_option doc.verso true

/-! Parent-schema compatibility through statements that retain the catalog. Foreign-key
enforcement and stored rows are unrestricted: this atom reads declarations and parent selection. -/

namespace Belay.Sqlite.Model

/-- For every supplied mapping, parent-schema compatibility has the row-write laws: removing
rows or storing an admitted row preserves it. The row-admission premise is unnecessary here.
Proof sketch: both row operations retain the catalog, which is the atom's only database input. -/
theorem parentSchemasCompatibleLaws (mapping : ForeignKeyMapping) :
    WriteLaws (Database.ParentSchemasCompatible mapping) where
  sublist _ _ _ holds _ := holds.catalog_eq rfl
  write _ _ _ _ holds _ _ _ := holds.catalog_eq rfl

/-- For every supplied mapping, row work, rules and input database with compatible parent
schemas, the row engine retains that schema fact on success and partial FAIL. Other errors
require nothing of their carrier. Triggers, actions, recursion depth, enforcement and stored
rows are unrestricted. Proof sketch: use the existing row-engine preservation theorem with
{name}`parentSchemasCompatibleLaws`; all its writes retain the catalog. -/
theorem rowsKeys_parentSchemasCompatible (mapping : ForeignKeyMapping) (rules : Resolved.WriteRules)
    (clock : Int) (target : Nat) (work : RowWork) {database : Database}
    (holds : database.ParentSchemasCompatible mapping) (plain : Bool) (algorithm : Option ConflictAlgorithm) :
    (rowsKeys rules clock target work database plain algorithm).effect.Satisfies
      (Database.ParentSchemasCompatible mapping) :=
  rowsKeys_satisfies (parentSchemasCompatibleLaws mapping) rules clock target work holds plain algorithm

/-- The statement is INSERT, UPDATE, UPSERT, DELETE, a query, a setting, a preparation error
or transaction control. These forms retain the catalog, including while their triggers and
actions write rows. CREATE, ADD COLUMN and DROP require their own schema conditions and do
not meet this sufficient condition. -/
def Resolved.Statement.KeepsParentSchema : Resolved.Statement → Prop
  | .begin | .commit | .rollback | .insert .. | .update .. | .upsert .. | .insertSelect .. | .delete ..
  | .prepareError _ | .query .. | .setting _ _ => True
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. | .addColumn .. | .drop .. => False

/-- Whether a statement meets the catalog-preserving condition is decidable from its form. -/
instance (statement : Resolved.Statement) : Decidable statement.KeepsParentSchema := by
  cases statement <;> simp only [Resolved.Statement.KeepsParentSchema] <;> infer_instance

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
  | createTable | createView | createIndex | createTrigger | addColumn | drop => exact False.elim met
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
