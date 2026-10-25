import Belay
import Belay.Sqlite.Model.ForeignKeyDropCatalog

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! Actual script outcomes distinguish successful actions, rejected parent drops and a
partial FAIL that keeps the parent catalog entry after its row and child key change. -/

open Belay.Sqlite Belay.Sqlite.Model
namespace ForeignKeyDropOutcomesFixture

/-- A real child key gives the DROP action work to perform. -/
def nullable : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k) ON DELETE SET NULL);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- The child action's AFTER trigger stops DROP after the row changes with a modeled FAIL. -/
def failRun : ScriptRun := nullable.raw.run (sql r"
  PRAGMA foreign_keys=ON;
  CREATE TRIGGER stop AFTER UPDATE ON c BEGIN SELECT RAISE(FAIL,'stop'); END;
  DROP TABLE p;")

/-- FAIL retains the parent catalog entry, removes its row and keeps the child's NULL update.
Both atoms hold in that partial state, rather than only in a restored input database. -/
theorem partialFail : failRun.outputs = [.done 0, .done 0, .error 19] ∧
    (failRun.connection.state.database.catalog.findTable (.ofString "p")).isSome = true ∧
    failRun.connection.state.database.rowsAt 0 = [] ∧
    (failRun.connection.state.database.rowsAt 1).map (·.values) = [[.null]] ∧
    failRun.connection.state.database.ParentSchemasCompatible failRun.connection.state.database.catalog.foreignKeyMapping ∧
    failRun.connection.state.database.RowReferencesHold failRun.connection.state.database.catalog.foreignKeyMapping := by
  decide +kernel

/-- CASCADE deletes the referenced child before removing its parent's catalog entry. -/
def cascading : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k) ON DELETE CASCADE);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- The final child is empty, so row truth survives although parent-schema compatibility fails. -/
theorem cascade : let result := cascading.raw.run (sql r"PRAGMA foreign_keys=ON; DROP TABLE p;")
    result.outputs = [.done 0, .done 0] ∧ result.connection.state.database.rowsAt 0 = [] ∧
    result.connection.state.database.RowReferencesHold result.connection.state.database.catalog.foreignKeyMapping ∧
    ¬result.connection.state.database.ParentSchemasCompatible result.connection.state.database.catalog.foreignKeyMapping := by
  decide +kernel

/-- With NO ACTION, a nonempty child rejects its parent's implicit deletion. -/
def noAction : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k));
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- The error leaves both original tables and matching rows, with both atoms true. -/
theorem rejected : let result := noAction.raw.run (sql r"PRAGMA foreign_keys=ON; DROP TABLE p;")
    result.outputs = [.done 0, .error 19] ∧ result.connection.state.database = noAction.raw ∧
    result.connection.state.database.ParentSchemasCompatible result.connection.state.database.catalog.foreignKeyMapping ∧
    result.connection.state.database.RowReferencesHold result.connection.state.database.catalog.foreignKeyMapping := by
  decide +kernel

/-- Explicit rollback restores the dropped parent and the child key from the saved snapshot. -/
theorem rollback : let result := nullable.raw.run (sql r"PRAGMA foreign_keys=ON; BEGIN; DROP TABLE p; ROLLBACK;")
    result.outputs = [.done 0, .done 0, .done 0, .done 0] ∧
    result.connection.state.database = nullable.raw ∧ result.connection.state.snapshot = none := by
  decide +kernel

end ForeignKeyDropOutcomesFixture
#print axioms ForeignKeyDropOutcomesFixture.partialFail
#print axioms ForeignKeyDropOutcomesFixture.cascade
#print axioms ForeignKeyDropOutcomesFixture.rejected
#print axioms ForeignKeyDropOutcomesFixture.rollback
