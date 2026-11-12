import ViewsSupport

set_option doc.verso true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

/-! Writes to a view and catalog statements on a view are checked through SQL: the model gives
the prepare error of SQLite, in its order, and refuses what it cannot place. The messages
are compared with native SQLite in the Python fixture. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open ViewExamples

namespace ViewWriteExamples

/-- A table, readable views, views that SQLite cannot read, a view whose query has an error that
SQLite finds only when a statement runs the view, and a trigger. -/
def database : Database := db! r"
  CREATE TABLE t(a INTEGER, b TEXT);
  CREATE VIEW v AS SELECT a, b FROM t;
  CREATE VIEW Mixed AS SELECT a FROM t;
  CREATE VIEW broken AS SELECT * FROM missing;
  CREATE VIEW cycle AS SELECT * FROM cycle;
  CREATE VIEW narrow(x, y) AS SELECT 1;
  CREATE VIEW badcol AS SELECT zz FROM t;
  CREATE VIEW scalar AS SELECT (SELECT a, b FROM t) AS x;
  CREATE VIEW w(x, y) AS SELECT 1;
  CREATE VIEW nest AS SELECT * FROM w;
  CREATE VIEW newv AS SELECT new.a FROM t;
  CREATE TRIGGER ex AFTER INSERT ON t BEGIN SELECT 1; END;
  CREATE TRIGGER body BEFORE INSERT ON t BEGIN INSERT INTO newv VALUES (1); END;"

/-- A write to a view stops at the first statement error, and the next statement runs. -/
theorem write_to_view_fails : (database.run (sql r"INSERT INTO v VALUES (1, 'x'); SELECT 1;")).outputs =
    [.error 1, .rows [[.integer 1]]] := by decide +kernel

/-- Model preparation messages are compared with native SQLite in the Python fixture. -/
def messages : List (Option String) := [
  prepareMessage (sql r"INSERT INTO v VALUES (1, 'x')") database,
  prepareMessage (sql r"INSERT INTO MIXED VALUES (1)") database,
  prepareMessage (sql r"INSERT INTO v VALUES (1), (1, 2)") database,
  prepareMessage (sql r"UPDATE v SET zz = 1 WHERE zz = 2") database,
  prepareMessage (sql r"DELETE FROM v WHERE zz = 1") database,
  prepareMessage (sql r"REPLACE INTO v VALUES (1, 2)") database,
  prepareMessage (sql r"INSERT INTO v VALUES (1, zz)") database,
  prepareMessage (sql r"INSERT INTO broken VALUES (1)") database,
  prepareMessage (sql r"UPDATE cycle SET a = 1") database,
  prepareMessage (sql r"DELETE FROM badcol") database,
  prepareMessage (sql r"INSERT INTO narrow VALUES (1)") database,
  prepareMessage (sql r"CREATE INDEX i ON v(a)") database,
  prepareMessage (sql r"CREATE INDEX i ON broken(a)") database,
  prepareMessage (sql r"CREATE INDEX t ON v(a)") database,
  prepareMessage (sql r"ALTER TABLE v ADD COLUMN c") database,
  prepareMessage (sql r"ALTER TABLE broken ADD COLUMN c") database,
  prepareMessage (sql r"CREATE TRIGGER tr AFTER INSERT ON v BEGIN SELECT 1; END") database,
  prepareMessage (sql r"CREATE TRIGGER tr BEFORE DELETE ON V BEGIN SELECT 1; END") database,
  prepareMessage (sql r"CREATE TRIGGER tr AFTER INSERT ON broken BEGIN SELECT 1; END") database,
  prepareMessage (sql r"CREATE TRIGGER ex AFTER INSERT ON v BEGIN SELECT 1; END") database,
  prepareMessage (sql r"CREATE TRIGGER IF NOT EXISTS ex AFTER INSERT ON v BEGIN SELECT 1; END") database,
  prepareMessage (sql r"INSERT INTO newv VALUES (1)") database]

/-- The width check of another view's name list is not part of the read of a view's columns, so
the model has no columns for a view over a view with a wrong-width name list: the write stays a
restriction, where SQLite reports {lit}`cannot modify nest because it is a view` (pinned in the
Python fixture). -/
example : restriction (sql r"INSERT INTO nest VALUES (1)") database = some ⟨[], .viewBodyCheck⟩ := by
  decide +kernel

/-- A write to a view inside a trigger body reads the view with the rows of the trigger in sight,
which the model's read does not: a column {lit}`new.a` that it cannot find makes the write that fires
the trigger a restriction, where SQLite reports {lit}`cannot modify newv because it is a view`
(pinned in the Python fixture). -/
example : (restriction (sql r"INSERT INTO t VALUES (1, 'x')") database).map (·.kind) = some .viewBodyCheck := by
  decide +kernel

/-- An error of the view's query that SQLite finds only when a statement runs the view stays a
restriction for a write to the view and for the pragma. -/
example : restriction (sql r"INSERT INTO scalar VALUES (1)") database = some ⟨[], .viewBodyCheck⟩ := by
  decide +kernel

/-- The pragma shares the restriction. -/
example : restriction (sql r"PRAGMA table_info(scalar)") database = some ⟨[], .viewBodyCheck⟩ := by
  decide +kernel

#eval IO.println ("write-messages:" ++ (Lean.toJson messages).compress)
#print axioms write_to_view_fails

end ViewWriteExamples
