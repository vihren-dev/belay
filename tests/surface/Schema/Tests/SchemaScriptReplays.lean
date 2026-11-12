import InsertSelectExamples

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! A fixture module of {lit}`tests/surface_schema_script_test.py`: scripts of the statements that the schema step laws
describe (ADR 0017, S6, task {lit}`20261027-schema-script-laws`), with the outputs that the model gives, for a check
against pinned SQLite. The scripts drop the parent of a foreign key with enforcement off and on, run the failing
CREATE TABLE, DROP TABLE, COMMIT and BEGIN, turn the enforcement on inside and outside a transaction, and run the
INSERT from a query that succeeds and the four that fail. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SchemaStepLaws InsertSelectExamples
namespace SchemaScriptReplays

/-- DROP TABLE of the parent with enforcement off, then a read of the child. The child keeps its three rows. -/
def dropOff : Script := sql r"DROP TABLE p; SELECT id, pid, note FROM c ORDER BY id;"

/-- DROP TABLE of the parent with enforcement on, then a read of the child. The cascade removes its rows. -/
def dropOn : Script := sql r"PRAGMA foreign_keys = ON; DROP TABLE p; SELECT id, pid, note FROM c ORDER BY id;"

/-- The failing CREATE TABLE and DROP TABLE, and the transaction statements out of order, then the settings. -/
def refusals : Script := sql r"
  CREATE TABLE p(id INTEGER);
  DROP TABLE zz;
  COMMIT;
  BEGIN;
  BEGIN;
  PRAGMA foreign_keys = ON;
  PRAGMA foreign_keys;
  COMMIT;
  PRAGMA foreign_keys = ON;
  PRAGMA foreign_keys;
  PRAGMA foreign_key_check;
  SELECT count(*) FROM c;"

/-- The INSERT from a query that succeeds, the four that fail, and a read of the target. -/
def inserts : Script := sql r"
  INSERT INTO dst SELECT id, name FROM src;
  INSERT INTO dst SELECT id, name FROM holes;
  INSERT INTO dstUnique SELECT id, name FROM src;
  INSERT INTO dstChecked SELECT id, name FROM src;
  INSERT INTO dstStrict SELECT id, name FROM src;
  SELECT id, name FROM dst ORDER BY id;"

open Lean Elab Meta in
/-- Keep exact model value tags so the test can compare native observations. -/
def outputJson : Output → Json
  | .rows rows => Json.mkObj [("rows", toJson rows)]
  | .done changes => Json.mkObj [("done", toJson changes)]
  | .error code => Json.mkObj [("error", toJson code)]
  | .oneOf results => Json.mkObj [("oneOf", toJson results)]
  | .unmodeled reason => Json.mkObj [("unmodeled", toJson reason)]

open Lean Elab Meta in
/-- Emit one replay of the S5 path: the SQL text, and the outputs that the model gives. -/
def emitReplay (name : String) (report : Replay.Report) : Term.TermElabM Unit := do
  logInfo m!"REPLAY:{(Json.mkObj [("name", toJson name), ("sql", toJson report.sqlite),
    ("outputs", toJson (report.outputs.map outputJson))]).compress}"

open Lean Elab Meta in
/-- Replay each script on the database it runs on. -/
elab "report_schema_replays" : command => Command.liftTermElabM do
  emitReplay "drop-off" (← Replay.scriptReport (mkConst ``family) (mkConst ``dropOff))
  emitReplay "drop-on" (← Replay.scriptReport (mkConst ``family) (mkConst ``dropOn))
  emitReplay "refusals" (← Replay.scriptReport (mkConst ``family) (mkConst ``refusals))
  emitReplay "inserts" (← Replay.scriptReport (mkConst ``warehouse) (mkConst ``inserts))

report_schema_replays

end SchemaScriptReplays
