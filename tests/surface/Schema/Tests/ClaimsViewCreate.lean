import ViewsSupport

set_option doc.verso true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

/-! CREATE VIEW is checked through SQL, actual execution, late resolution and
the existing generic validity proof. Native comparisons check error precedence. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open ViewExamples

namespace ViewCreateExamples

/-- A table, index, view and trigger exercise the two catalog namespaces. -/
def database : Database := db! r"
  CREATE TABLE MixedT(x INTEGER); INSERT INTO MixedT VALUES(7),(8);
  CREATE INDEX idx ON MixedT(x); CREATE VIEW MixedV AS SELECT x FROM MixedT;
  CREATE TRIGGER tr AFTER INSERT ON MixedT BEGIN SELECT 1; END;"

/-- A view can precede its referenced table and later read the inserted row. -/
theorem late_table : (Database.empty.run (sql r"
    CREATE VIEW v(a) AS SELECT x FROM t;
    CREATE TABLE t(x INTEGER); INSERT INTO t VALUES(7); SELECT a FROM v;
  ")).outputs = [.done 0, .done 0, .done 1, .rows [[.integer 7]]] := by decide +kernel

/-- Creation stores no rows for a view, even when its SELECT reads stored rows. -/
theorem empty_storage : database.raw.rows[2]? = some [] ∧
    (database.catalog.findView (name! "MixedV")).isSome = true := by decide +kernel

/-- A missing reference does not prevent creation; using the view then fails. -/
theorem missing_use : (Database.empty.run (sql r"
    CREATE VIEW v AS SELECT * FROM missing; SELECT * FROM v;
  ")).outputs = [.done 0, .error 1] := by decide +kernel

/-- A self-reference is stored and gives the native cycle error only when used. -/
theorem cycle_use : prepareMessage (sql r"SELECT * FROM v")
    (db! r"CREATE VIEW v AS SELECT * FROM v;") = some "view v is circularly defined" := by decide +kernel

/-- Explicit names are checked against the resolved width when the view is used. -/
theorem columns_use : prepareMessage (sql r"SELECT * FROM v")
    (db! r"CREATE VIEW v(a,b) AS SELECT 1;") = some "expected 2 columns for 'v' but got 1" := by decide +kernel

/-- Dropping and recreating a source does not leave a stale resolved column in a view. -/
theorem changed_source : prepareMessage (sql r"SELECT * FROM v")
    (db! r"CREATE TABLE t(x); CREATE VIEW v AS SELECT x FROM t; DROP TABLE t; CREATE TABLE t(y);") =
      some "no such column: x" := by decide +kernel

/-- IF NOT EXISTS preserves the existing table and view, including their definitions. -/
theorem if_not_exists : (database.run (sql r"
    CREATE VIEW IF NOT EXISTS mixedt AS SELECT * FROM missing;
    CREATE VIEW IF NOT EXISTS mixedv(a,b) AS SELECT 1;
  ")).db.raw = database.raw := by decide +kernel

/-- Trigger names are separate, so a view can have the name of an existing trigger. -/
theorem trigger_namespace : (database.run (sql r"CREATE VIEW tr AS SELECT 1;")).outputs = [.done 0] := by
  decide +kernel

/-- Rolling back a new view restores the complete pre-transaction database. -/
theorem rollback : (database.run (sql r"BEGIN; CREATE VIEW fresh AS SELECT 1; ROLLBACK;")).db.raw =
    database.raw := by decide +kernel

/-- CREATE VIEW and its IF NOT EXISTS no-op preserve the counters of an earlier INSERT. -/
theorem counters : (Database.empty.run (sql r"
    CREATE TABLE t(x); INSERT INTO t VALUES(1); CREATE VIEW v AS SELECT x FROM t;
    CREATE VIEW IF NOT EXISTS v AS SELECT 2; SELECT changes(), total_changes();
  ") Env.newConnection).outputs = [.done 0, .done 1, .done 0, .done 0, .rows [[.integer 1, .integer 1]]] := by decide +kernel

/-- Every initial valid database remains valid after any written CREATE VIEW,
including prepare errors and unresolved bodies. The actual public runner carries the proof. -/
theorem create_valid (db : Database) (name : Identifier) (ifNotExists : Bool)
    (columns : Option (List Identifier)) (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) :
    (db.run (⟨[(.createView name ifNotExists columns query subqueries, [])]⟩ : Script)).db.raw.Valid Profile.pinned :=
  (db.run (⟨[(.createView name ifNotExists columns query subqueries, [])]⟩ : Script)).db.valid

/-- Model preparation messages are compared with native SQLite in the Python fixture. -/
def messages : List (Option String) := [
  prepareMessage (sql r"CREATE VIEW mixedt AS SELECT 1") database,
  prepareMessage (sql r"CREATE VIEW mixedv AS SELECT 1") database,
  prepareMessage (sql r"CREATE VIEW IF NOT EXISTS idx AS SELECT 1") database,
  prepareMessage (sql r"CREATE VIEW sqlite_x AS SELECT 1") database,
  prepareMessage ((sql r"CREATE VIEW sqlite_x AS SELECT ?") .null) database,
  prepareMessage ((sql r"CREATE VIEW IF NOT EXISTS mixedt AS SELECT ?") .null) database,
  prepareMessage ((sql r"CREATE VIEW IF NOT EXISTS mixedv AS WITH unused AS (SELECT ?) SELECT 1") .null) database,
  prepareMessage ((sql r"CREATE VIEW fresh AS SELECT (SELECT ?)") .null) database,
  prepareMessage (sql r"CREATE VIEW fresh AS SELECT * FROM missing") database,
  prepareMessage (sql r"CREATE VIEW fresh AS SELECT * FROM fresh") database,
  prepareMessage (sql r"CREATE VIEW tr AS SELECT 1") database,
  prepareMessage (sql r"CREATE VIEW IF NOT EXISTS mixedt AS SELECT * FROM missing") database,
  prepareMessage (sql r"CREATE VIEW fresh(a,b) AS SELECT 1") database]

#eval IO.println ("create-messages:" ++ (Lean.toJson messages).compress)
#print axioms late_table
#print axioms empty_storage
#print axioms missing_use
#print axioms cycle_use
#print axioms columns_use
#print axioms changed_source
#print axioms if_not_exists
#print axioms trigger_namespace
#print axioms rollback
#print axioms counters
#print axioms create_valid

end ViewCreateExamples
