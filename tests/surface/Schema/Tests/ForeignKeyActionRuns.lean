import Belay

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! Actual runs of the actions that earlier fixtures do not run: RESTRICT against NO ACTION,
SET DEFAULT and a deferred key. Each run is also a native comparison: the outputs, the rows and
the two atoms agree with SQLite 3.51.0. The general laws cover these actions through the
action-independent conditions of the engine; these runs show the cases that differ. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyActionRunsFixture

/-- Both foreign-key atoms of a database under the mapping that its own catalog selects. -/
abbrev Atoms (database : Model.Database) : Prop :=
  database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
    database.RowReferencesHold database.catalog.foreignKeyMapping

/-- The child references the parent with NO ACTION, and a trigger inserts each deleted parent row
again. The child is satisfied again at the end of the statement. -/
def noActionTrigger : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k) ON DELETE NO ACTION);
  CREATE TRIGGER back AFTER DELETE ON p BEGIN INSERT INTO p VALUES(old.k); END;
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- The same schema with RESTRICT, which reports the child as soon as the parent row goes. -/
def restrictTrigger : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k) ON DELETE RESTRICT);
  CREATE TRIGGER back AFTER DELETE ON p BEGIN INSERT INTO p VALUES(old.k); END;
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- NO ACTION checks at the end of the statement. The trigger has put the parent row back, so the
delete succeeds, the table keeps its row and both atoms hold. -/
theorem noActionRepairs : let result := noActionTrigger.raw.run (sql r"PRAGMA foreign_keys=ON; DELETE FROM p;")
    result.outputs = [.done 0, .done 1] ∧ (result.connection.state.database.rowsAt 0).map (·.values) = [[.integer 1]] ∧
    Atoms result.connection.state.database := by decide +kernel

/-- RESTRICT fails with the constraint error although the trigger would repair the parent. The
error keeps the input database, so both atoms still hold. -/
theorem restrictRefuses : let result := restrictTrigger.raw.run (sql r"PRAGMA foreign_keys=ON; DELETE FROM p;")
    result.outputs = [.done 0, .error 19] ∧ result.connection.state.database = restrictTrigger.raw ∧
    Atoms result.connection.state.database := by decide +kernel

/-- With foreign keys off, RESTRICT is not run: the same delete removes the parent row for good and
the database keeps its catalog, so only the row atom fails. -/
theorem restrictOff : let result := (db! r"
      CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k) ON DELETE RESTRICT);
      INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);").raw.run (sql r"DELETE FROM p;")
    result.outputs = [.done 1] ∧ result.connection.state.database.rowsAt 0 = [] ∧
    ¬ result.connection.state.database.RowReferencesHold result.connection.state.database.catalog.foreignKeyMapping ∧
    result.connection.state.database.ParentSchemasCompatible result.connection.state.database.catalog.foreignKeyMapping := by
  decide +kernel

/-- The default of the child is 0, which the parent has, so SET DEFAULT can write it. -/
def setDefault : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY);
  CREATE TABLE c(x DEFAULT 0 REFERENCES p(k) ON DELETE SET DEFAULT ON UPDATE SET DEFAULT);
  INSERT INTO p VALUES(0),(1); INSERT INTO c VALUES(1);"

/-- Deleting the referenced parent row writes the default into the child, and both atoms hold. -/
theorem setDefaultDelete : let result := setDefault.raw.run (sql r"PRAGMA foreign_keys=ON; DELETE FROM p WHERE k = 1;")
    result.outputs = [.done 0, .done 1] ∧ (result.connection.state.database.rowsAt 1).map (·.values) = [[.integer 0]] ∧
    Atoms result.connection.state.database := by decide +kernel

/-- Changing the referenced key writes the default into the child, not the new key. -/
theorem setDefaultUpdate : let result := setDefault.raw.run (sql r"PRAGMA foreign_keys=ON; UPDATE p SET k = 2 WHERE k = 1;")
    result.outputs = [.done 0, .done 1] ∧ (result.connection.state.database.rowsAt 1).map (·.values) = [[.integer 0]] ∧
    Atoms result.connection.state.database := by decide +kernel

/-- The parent has no row for the default 0 of the child. -/
def defaultWithoutParent : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x DEFAULT 0 REFERENCES p(k) ON DELETE SET DEFAULT);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- The written default has no parent, so the statement fails and keeps the input database. SET
DEFAULT is no escape from the check: this is the condition that the general laws keep. -/
theorem setDefaultWithoutParent : let result := defaultWithoutParent.raw.run (sql r"PRAGMA foreign_keys=ON; DELETE FROM p;")
    result.outputs = [.done 0, .error 19] ∧ result.connection.state.database = defaultWithoutParent.raw ∧
    Atoms result.connection.state.database := by decide +kernel

/-- A key that is DEFERRABLE INITIALLY DEFERRED, with a child row that has a parent. -/
def deferred : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k) DEFERRABLE INITIALLY DEFERRED);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- With foreign keys on, a write that processes a deferred key is a restriction: the run stops at
it with an unmodeled output, the later statement does not run and the database is the input. The
current result is kept: no law claims what SQLite does at the commit. -/
theorem deferredStops : let script : Script := sql r"PRAGMA foreign_keys=ON; INSERT INTO c VALUES(2); INSERT INTO c VALUES(1);"
    let result := deferred.raw.run script
    result.outputs.map Output.endsRun = [false, true] ∧ result.connection.state.database = deferred.raw ∧
    Atoms result.connection.state.database := by decide +kernel

/-- With foreign keys off, the same key is not processed. The orphan is stored, so row truth fails
while the catalog stays compatible. -/
theorem deferredOff : let result := deferred.raw.run (sql r"INSERT INTO c VALUES(2);")
    result.outputs = [.done 1] ∧
    ¬ result.connection.state.database.RowReferencesHold result.connection.state.database.catalog.foreignKeyMapping ∧
    result.connection.state.database.ParentSchemasCompatible result.connection.state.database.catalog.foreignKeyMapping := by
  decide +kernel

end ForeignKeyActionRunsFixture

#print axioms ForeignKeyActionRunsFixture.noActionRepairs
#print axioms ForeignKeyActionRunsFixture.restrictRefuses
#print axioms ForeignKeyActionRunsFixture.restrictOff
#print axioms ForeignKeyActionRunsFixture.setDefaultDelete
#print axioms ForeignKeyActionRunsFixture.setDefaultUpdate
#print axioms ForeignKeyActionRunsFixture.setDefaultWithoutParent
#print axioms ForeignKeyActionRunsFixture.deferredStops
#print axioms ForeignKeyActionRunsFixture.deferredOff
