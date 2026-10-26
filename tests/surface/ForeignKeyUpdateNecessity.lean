import Belay
import Belay.Sqlite.Model.ForeignKeyUpdateBound

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 1074

/-! Input and effect restrictions of the UPDATE preservation law are necessary.
The stale self scan matches a pinned native SQLite 3.51.0 diagnostic. Generated-cell
consistency is a separate requirement for raw databases, which Valid does not enforce. -/

open Belay.Sqlite
namespace ForeignKeyUpdateNecessityFixture

/-- Deleting the external parent creates one pending violation before the trigger runs. -/
def input : Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p);
  CREATE TABLE s(k UNIQUE,y REFERENCES s(k));
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1); INSERT INTO s VALUES(1,1);"

/-- A level-1 UPDATE scans its stale self row while another table has a pending violation. -/
def staleResult : ScriptRun := input.raw.run (sql r"
  PRAGMA foreign_keys=ON;
  CREATE TRIGGER t AFTER DELETE ON p BEGIN UPDATE s SET k=1; END;
  DELETE FROM p;")

/-- Both FK atoms hold before the write, as does Valid. None prevents the stale scan. -/
theorem startsSatisfied : input.raw.Valid .pinned ∧
    input.raw.ParentSchemasCompatible input.raw.catalog.foreignKeyMapping ∧
    input.raw.RowReferencesHold input.raw.catalog.foreignKeyMapping := by
  exact ⟨input.valid, by decide +kernel, by decide +kernel⟩

/-- The actual DELETE succeeds and retains an orphan after the stale self scan cancels
its pending counter. This refutes unconditional enforcement preservation. -/
theorem staleScanLeavesOrphan : staleResult.outputs = [.done 0, .done 0, .done 1] ∧
    staleResult.connection.state.database.foreignKeyViolations = 1 := by
  decide +kernel

/-- Changing the self-child key as well selects level 2, removes the stale row, and makes
the final counter reject the outer DELETE. -/
theorem changedSelfChildRejects :
    let result := input.raw.run (sql r"
      PRAGMA foreign_keys=ON;
      CREATE TRIGGER t AFTER DELETE ON p BEGIN UPDATE s SET k=1,y=1; END;
      DELETE FROM p;")
    result.outputs = [.done 0, .done 0, .error 19] ∧
      result.connection.state.database.foreignKeyViolations = 0 := by
  decide +kernel

/-- A parent action also selects level 2, so the same unchanged-value UPDATE does not
cancel the unrelated pending violation. -/
def actionInput : Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p);
  CREATE TABLE s(k UNIQUE,y REFERENCES s(k) ON UPDATE CASCADE);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1); INSERT INTO s VALUES(1,1);"

/-- With that action, the outer DELETE fails and its original parent row is restored. -/
theorem parentActionRejects :
    let result := actionInput.raw.run (sql r"
      PRAGMA foreign_keys=ON;
      CREATE TRIGGER t AFTER DELETE ON p BEGIN UPDATE s SET k=1; END;
      DELETE FROM p;")
    result.outputs = [.done 0, .done 0, .error 19] ∧
      result.connection.state.database.foreignKeyViolations = 0 := by
  decide +kernel

/-- This ordinary schema has a generated FK child cell and an independent payload. -/
def generatedInput : Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(a,y AS(a) REFERENCES p,x);
  INSERT INTO p VALUES(1); INSERT INTO c(a,x) VALUES(1,0);"

/-- The raw primitive permits a stale generated cell, despite stored types and valid references. -/
def staleGenerated : Database.Raw := generatedInput.raw.setRows 1
  [{ rowid := 1, values := [.integer 9, .integer 1, .integer 0] }]

/-- Valid and both FK atoms do not require agreement between a generated cell and its expression. -/
theorem staleGeneratedEntry : staleGenerated.Valid .pinned ∧
    staleGenerated.ParentSchemasCompatible staleGenerated.catalog.foreignKeyMapping ∧
    staleGenerated.RowReferencesHold staleGenerated.catalog.foreignKeyMapping := by
  decide +kernel

/-- Updating only the payload recomputes the stale generated key without marking it changed,
so preservation needs a consistent-generated-values input or an explicit key-coverage premise. -/
theorem staleGeneratedLeavesOrphan :
    let result := staleGenerated.run (sql "PRAGMA foreign_keys=ON; UPDATE c SET x=1;")
    result.outputs = [.done 0, .done 1] ∧ result.connection.state.database.foreignKeyViolations = 1 := by
  decide +kernel

end ForeignKeyUpdateNecessityFixture

#print axioms ForeignKeyUpdateNecessityFixture.startsSatisfied
#print axioms ForeignKeyUpdateNecessityFixture.staleScanLeavesOrphan
#print axioms ForeignKeyUpdateNecessityFixture.changedSelfChildRejects
#print axioms ForeignKeyUpdateNecessityFixture.parentActionRejects
#print axioms ForeignKeyUpdateNecessityFixture.staleGeneratedEntry
#print axioms ForeignKeyUpdateNecessityFixture.staleGeneratedLeavesOrphan
