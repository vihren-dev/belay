import ViewsSupport

set_option doc.verso true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

/-! DROP VIEW uses the shared statement runner, preserves stored rows, and does
not resolve the removed definition. CREATE VIEW syntax is a later task unit. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open ViewExamples

namespace ViewDropExamples

/-- A physical table and index followed by ordinary, invalid and cyclic views. -/
def physical : Database := db! r"
  CREATE TABLE MixedT(x INTEGER); INSERT INTO MixedT VALUES(7),(8);
  CREATE INDEX idx ON MixedT(x);"

/-- These definitions have exactly the native prelude used by the Python test. -/
def database : Database := ⟨withViews physical [
  (name! "MixedV", definition (sql r"SELECT x FROM MixedT")),
  (name! "broken", definition (sql r"SELECT * FROM missing")),
  (name! "cycle", definition (sql r"SELECT * FROM cycle")),
  (name! "nested", definition (sql r"SELECT x FROM MixedV"))], by decide +kernel⟩

/-- Dropping a view produces a successful zero-row write output. -/
theorem drop_output : (database.run (sql r"DROP VIEW mixedv")).outputs = [.done 0] := by decide +kernel

/-- Execution removes only the view's catalog position and its empty storage. -/
theorem drop_database : (database.run (sql r"DROP VIEW mixedv")).db.raw = database.raw.drop [2] := by
  decide +kernel

/-- Later objects shift position, with all physical table rows retained. -/
theorem shifted_positions :
    ((database.run (sql r"DROP VIEW mixedv")).db.catalog.findView (name! "nested")).map Prod.fst = some 4 ∧
    (database.run (sql r"DROP VIEW mixedv")).db.raw.rows = database.raw.rows.take 2 ++ [[], [], []] := by
  decide +kernel

/-- A dependent view looks up the dropped name again and reports the missing source. -/
theorem late_lookup : prepareMessage (sql r"SELECT * FROM nested")
    (database.run (sql r"DROP VIEW mixedv")).db = some "no such table: main.MixedV" := by decide +kernel

/-- Rollback restores the entire database and leaves the view available to a later query. -/
theorem rollback :
    (database.run (sql r"BEGIN; DROP VIEW mixedv; ROLLBACK")).db.raw = database.raw ∧
    (database.run (sql r"BEGIN; DROP VIEW mixedv; ROLLBACK; SELECT x FROM MixedV ORDER BY x")).outputs =
      [.done 0, .done 0, .done 0, .rows [[.integer 7], [.integer 8]]] := by decide +kernel

/-- Missing sources and cycles inside removed views do not prevent their removal. -/
theorem unresolved_drop : (database.run (sql r"DROP VIEW broken; DROP VIEW cycle")).outputs = [.done 0, .done 0] := by
  decide +kernel

/-- IF EXISTS removes nothing for an absent name or an index, preserving the database. -/
theorem absent_drop :
    (database.run (sql r"DROP VIEW IF EXISTS missing; DROP VIEW IF EXISTS idx")).db.raw = database.raw ∧
    (database.run (sql r"DROP VIEW IF EXISTS missing; DROP VIEW IF EXISTS idx")).outputs = [.done 0, .done 0] := by
  decide +kernel

/-- A wrong-kind prepare error leaves the table and every row intact. -/
theorem wrong_kind : (database.run (sql r"DROP VIEW IF EXISTS mixedt")).outputs = [.error 1] ∧
    (database.run (sql r"DROP VIEW IF EXISTS mixedt")).db.raw = database.raw := by decide +kernel

/-- The public runner preserves validity for every initial valid database and
every view name, whether the drop succeeds or reports a prepare error. -/
theorem drop_valid (db : Database) (name : Identifier) (ifExists : Bool) :
    (db.run (⟨[(.dropView name ifExists, [])]⟩ : Script)).db.raw.Valid Profile.pinned :=
  (db.run (⟨[(.dropView name ifExists, [])]⟩ : Script)).db.valid

/-- Messages from the model's resolver, compared with native SQLite by the test. -/
def messages : List (Option String) := [
  prepareMessage (sql r"DROP VIEW mixedt") database,
  prepareMessage (sql r"DROP VIEW IF EXISTS mixedt") database,
  prepareMessage (sql r"DROP TABLE mixedv") database,
  prepareMessage (sql r"DROP TABLE IF EXISTS mixedv") database,
  prepareMessage (sql r"DROP VIEW MiSsInG") database,
  prepareMessage (sql r"DROP VIEW idx") database,
  prepareMessage (sql r"DROP VIEW IF EXISTS sqlite_schema") database,
  prepareMessage (sql r"DROP VIEW IF EXISTS missing") database,
  prepareMessage (sql r"DROP VIEW IF EXISTS idx") database,
  prepareMessage (sql r"DROP VIEW broken") database,
  prepareMessage (sql r"DROP VIEW cycle") database]

#eval IO.println ("drop-messages:" ++ (Lean.toJson messages).compress)
#print axioms drop_output
#print axioms drop_database
#print axioms shifted_positions
#print axioms late_lookup
#print axioms rollback
#print axioms unresolved_drop
#print axioms absent_drop
#print axioms wrong_kind
#print axioms drop_valid

end ViewDropExamples
