import RebuildGuide

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! A fixture module of {lit}`tests/surface_rebuild_test.py`: the rebuilds of the guide with a read of the sessions
after them, with the outputs that the model gives, for a check against pinned SQLite (ADR 0017, S6, part 2). The four
runs are the rebuild in the right order, the wrong rebuild on a connection with foreign keys on, the right rebuild on
a database with a customer without a name, and the right rebuild on a database with a session of a customer that
does not exist. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildReplays
open RebuildGuide

/-- A database of the guide's schema with a customer without a name. The copy into the rebuilt table must refuse
it. -/
def withoutName : Belay.Sqlite.Database := db! r"
  CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions(id INTEGER PRIMARY KEY, customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);
  INSERT INTO customers VALUES(1,'ada','Ada@X'),(2,NULL,'B@X');
  INSERT INTO sessions VALUES(10,1,100);"

/-- A database of the guide's schema with a session of customer 99, who does not exist. Foreign keys are off while
the database is built, so SQLite stores it. -/
def dangling : Belay.Sqlite.Database := db! r"
  CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions(id INTEGER PRIMARY KEY, customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);
  INSERT INTO customers VALUES(1,'ada','Ada@X');
  INSERT INTO sessions VALUES(10,1,100),(11,99,200);"

/-- The rebuild of the guide, and the read of the sessions. -/
def rightThenRead : Script := sql r"
  PRAGMA foreign_keys = OFF;
  BEGIN;
  CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT NOT NULL, email TEXT NOT NULL);
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  PRAGMA foreign_key_check;
  COMMIT;
  PRAGMA foreign_keys = ON;
  SELECT id, customer_id, expires_at FROM sessions ORDER BY id;"

/-- The wrong rebuild on a connection with foreign keys on, and the read of the sessions. -/
def wrongThenRead : Script := sql r"
  PRAGMA foreign_keys = ON;
  BEGIN;
  PRAGMA foreign_keys = OFF;
  CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT NOT NULL, email TEXT NOT NULL);
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  COMMIT;
  SELECT id, customer_id, expires_at FROM sessions ORDER BY id;"

open Lean Elab Meta in
/-- Keep exact model value tags so the test can compare native observations. -/
def outputJson : Output → Json
  | .rows rows => Json.mkObj [("rows", toJson rows)]
  | .done changes => Json.mkObj [("done", toJson changes)]
  | .error code => Json.mkObj [("error", toJson code)]
  | .oneOf results => Json.mkObj [("oneOf", toJson results)]
  | .unmodeled reason => Json.mkObj [("unmodeled", toJson reason)]

open Lean Elab Meta in
/-- Emit one replay: the SQL text, and the outputs that the model gives. -/
def emitReplay (name : String) (report : Replay.Report) : Term.TermElabM Unit := do
  logInfo m!"REPLAY:{(Json.mkObj [("name", toJson name), ("sql", toJson report.sqlite),
    ("outputs", toJson (report.outputs.map outputJson))]).compress}"

open Lean Elab Meta in
/-- Replay each script on the database it runs on. -/
elab "report_rebuild_replays" : command => Command.liftTermElabM do
  emitReplay "right" (← Replay.scriptReport (mkConst ``sample) (mkConst ``rightThenRead))
  emitReplay "wrong-enforced" (← Replay.scriptReport (mkConst ``sample) (mkConst ``wrongThenRead))
  emitReplay "without-name" (← Replay.scriptReport (mkConst ``withoutName) (mkConst ``rightThenRead))
  emitReplay "dangling" (← Replay.scriptReport (mkConst ``dangling) (mkConst ``rightThenRead))

report_rebuild_replays

end RebuildReplays
