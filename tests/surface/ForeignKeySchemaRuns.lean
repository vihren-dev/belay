import Belay
import Belay.Sqlite.Model.ForeignKeySchemaRuns

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! The schema atom survives data writes independently of row truth. The generic run law
includes rollback, and a bad saved snapshot demonstrates why its entry condition is needed. -/

open Belay.Sqlite
open Belay.Sqlite.Model (SqlState Outcome runSql runSqlFrom RunConditionsWith)

/-- A matching child whose parent deletion cascades when enforcement is enabled. -/
def matching : Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p ON DELETE CASCADE);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- A database whose foreign-key declaration has a nonunique parent. -/
def incompatible : Database := db! r"CREATE TABLE p(k); CREATE TABLE c(x REFERENCES p(k));"

/-- The resolved engine performs a cascading deletion and then restores the transaction. -/
def cascadeRollback : List (Model.Resolved.Statement × List Value) :=
  [(.begin, []), (.delete 0 none [] [] (some { depth := 4, keys := true }), []), (.rollback, [])]

/-- Every outcome database retains the schema atom by the public run theorem. -/
theorem cascadeRollbackCompatible : (runSql cascadeRollback matching.raw).Holds
    (fun database => database.ParentSchemasCompatible matching.raw.catalog.foreignKeyMapping) := by
  apply Belay.Sqlite.Model.runSql_parentSchemasCompatible _ _ (by decide +kernel)
  exact RunConditionsWith.of_unconditioned
    (unconditioned := fun statement => decide statement.KeepsParentSchema)
    (fun _ _ accepted => of_decide_eq_true accepted) _ _ _ (by decide +kernel)

example : (match runSql cascadeRollback matching.raw with
  | .success database => database == matching.raw
  | _ => false) = true := by decide +kernel

/-- With enforcement off, deleting the parent preserves schema compatibility but leaves an orphan. -/
def withoutEnforcement : ScriptRun := matching.raw.run (sql "DELETE FROM p;")

example : withoutEnforcement.outputs = [.done 1] ∧
    withoutEnforcement.connection.state.database.ParentSchemasCompatible matching.raw.catalog.foreignKeyMapping ∧
    ¬withoutEnforcement.connection.state.database.RowReferencesHold matching.raw.catalog.foreignKeyMapping := by
  decide +kernel

/-- The current database can be compatible even when an already-saved snapshot is incompatible. -/
def badSnapshot : SqlState := { database := matching.raw, snapshot := some incompatible.raw }

example : badSnapshot.database.ParentSchemasCompatible matching.raw.catalog.foreignKeyMapping ∧
    ¬(runSqlFrom 0 [(.rollback, [])] badSnapshot).Holds
      (fun database => database.ParentSchemasCompatible matching.raw.catalog.foreignKeyMapping) := by
  decide +kernel

#print axioms Belay.Sqlite.Model.parentSchemasCompatibleLaws
#print axioms Belay.Sqlite.Model.rowsKeys_parentSchemasCompatible
#print axioms Belay.Sqlite.Model.runStatement_parentSchemasCompatible
#print axioms Belay.Sqlite.Model.parentSchemasCompatibleKeeps
#print axioms Belay.Sqlite.Model.runSqlFrom_parentSchemasCompatible
#print axioms Belay.Sqlite.Model.runSql_parentSchemasCompatible
#print axioms Belay.Sqlite.Model.runScriptFrom_parentSchemasCompatible
#print axioms cascadeRollbackCompatible
