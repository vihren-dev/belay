import Belay

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

/-! A fixture module of {lit}`tests/surface_rebuild_affinity_test.py`: a table rebuild that changes the declared type of a
column loses information, although it succeeds and keeps every row (ADR 0017, S6, migration patterns). The table
{lit}`addresses` has a TEXT column {lit}`zip` with the values '01234' and 'n/a'. The rebuild creates a table whose
{lit}`zip` column has INTEGER affinity, copies the rows, drops the old table and renames the new one. INTEGER affinity
turns the text '01234' into the integer 1234, and the text 'n/a', which is not a number, stays text. A STRICT table
refuses the second value instead. The claim that the rebuild preserves the query of the {lit}`id` and {lit}`zip`
columns is false. The fixture emits the SQL of each run for the native check. -/

namespace RebuildAffinity
open Belay.Sqlite

/-- A complete environment with a constant clock and the counters after the setup INSERT. -/
def environment : Env :=
  { clock := some (fun _ => 0)
    counters := { changes := some 2, totalChanges := some 2, lastInsertRowid := some 2 } }

/-- Two addresses whose zip codes are text: one is a number with a leading zero, and one is not a number. -/
def addresses : Belay.Sqlite.Database := db! r"
  CREATE TABLE addresses(id INTEGER PRIMARY KEY, zip TEXT);
  INSERT INTO addresses VALUES(1, '01234'), (2, 'n/a');"

/-- The rebuild that changes the type of {lit}`zip` from TEXT to INTEGER. -/
def zipRebuild : Script := sql r"
  BEGIN;
  CREATE TABLE addresses_new(id INTEGER PRIMARY KEY, zip INTEGER);
  INSERT INTO addresses_new SELECT id, zip FROM addresses;
  DROP TABLE addresses;
  ALTER TABLE addresses_new RENAME TO addresses;
  COMMIT;"

/-- The same rebuild into a STRICT table. -/
def strictRebuild : Script := sql r"
  BEGIN;
  CREATE TABLE addresses_new(id INTEGER PRIMARY KEY, zip INTEGER) STRICT;
  INSERT INTO addresses_new SELECT id, zip FROM addresses;
  DROP TABLE addresses;
  ALTER TABLE addresses_new RENAME TO addresses;
  COMMIT;"

/-- The query that the rebuild should preserve. -/
def zipRows : Script := sql r"SELECT id, zip FROM addresses ORDER BY id"

/-- The rebuild and the query after it, as one script. -/
def rebuildThenRows : Script := sql r"
  BEGIN;
  CREATE TABLE addresses_new(id INTEGER PRIMARY KEY, zip INTEGER);
  INSERT INTO addresses_new SELECT id, zip FROM addresses;
  DROP TABLE addresses;
  ALTER TABLE addresses_new RENAME TO addresses;
  COMMIT;
  SELECT id, zip FROM addresses ORDER BY id;"

/-- {name}`rebuildThenRows` is the rebuild followed by the query. Proof sketch: the parsed statements are the same
terms. -/
theorem rebuildThenRows_is_the_rebuild_and_the_query : rebuildThenRows = zipRebuild ++ zipRows := rfl

/-- The copy into a STRICT table, and the number of rows that it stored. -/
def strictCopy : Script := sql r"
  CREATE TABLE addresses_new(id INTEGER PRIMARY KEY, zip INTEGER) STRICT;
  INSERT INTO addresses_new SELECT id, zip FROM addresses;
  SELECT count(*) FROM addresses_new;"

/-- The query before the rebuild returns both zip codes as text. Proof sketch: kernel evaluation of the run. -/
theorem rows_before : (addresses.run zipRows).outputs = [.rows [[1, "01234"], [2, "n/a"]]] := by
  decide +kernel

/-- The rebuild succeeds: every statement gives a result without an error, and the run does not stop. Proof sketch:
kernel evaluation of the run. -/
theorem rebuild_succeeds : (addresses.run zipRebuild).outputs.allOk = true := by decide +kernel

/-- After the rebuild, the zip code '01234' is the integer 1234, and 'n/a' is still text. Plain words: the rebuild
changes a stored value, and it keeps the value that is not a number. Proof sketch: kernel evaluation of the run. -/
theorem rows_after :
    (addresses.run rebuildThenRows).outputs.getLast? = some (.rows [[1, 1234], [2, "n/a"]]) := by
  decide +kernel

/-- The rebuild does not preserve the query, on the database {lit}`addresses` and its environment. Plain words: the
rebuild succeeds there, and the rows of the query before and after it differ. Proof sketch: the weak preservation
compares the actual values, and {name}`rows_before` and {name}`rows_after` separate them. -/
theorem rebuild_not_preserved :
    ¬ Migration.QueryPreserves (send zipRebuild) zipRows (fun _ => True) := by
  intro claim
  have same := congrArg Prod.fst
    (observationProfile_actual
      (claim addresses True.intro environment ⟨rfl, rfl, rfl, rfl⟩ ⟨True.intro, by decide +kernel⟩))
  change ((send zipRows).runFrom (ExecutionContext.initial addresses environment).clock
      (ExecutionContext.initial addresses environment).index (ExecutionContext.initial addresses environment).connection).value =
    ((Migration.after (send zipRebuild) (send zipRows)).runFrom (ExecutionContext.initial addresses environment).clock
      (ExecutionContext.initial addresses environment).index
      (ExecutionContext.initial addresses environment).connection).value at same
  have before : ((send zipRows).runFrom (ExecutionContext.initial addresses environment).clock
      (ExecutionContext.initial addresses environment).index
      (ExecutionContext.initial addresses environment).connection).value =
      some [.rows [[1, "01234"], [2, "n/a"]]] := by decide +kernel
  have after : ((Migration.after (send zipRebuild) (send zipRows)).runFrom
      (ExecutionContext.initial addresses environment).clock (ExecutionContext.initial addresses environment).index
      (ExecutionContext.initial addresses environment).connection).value =
      some [.rows [[1, 1234], [2, "n/a"]]] := by decide +kernel
  rw [before, after] at same
  cases same

/-- A STRICT table refuses the text 'n/a' instead of keeping it: the copy ends with an error, and the rebuild does
not succeed. Proof sketch: kernel evaluation of the run. -/
theorem strict_rebuild_fails : (addresses.run strictRebuild).outputs.allOk = false := by decide +kernel

/-- The copy into a STRICT table stores no row: the INSERT ends with the constraint error for a value of the wrong
type, which is SQLite's result code 19, and the table stays empty. Plain words: only a STRICT table refuses the text
'n/a'. Proof sketch: kernel evaluation of the run. -/
theorem strict_copy_stores_nothing :
    (addresses.run strictCopy).outputs = [.done 0, .error 19, .rows [[0]]] := by decide +kernel

#print axioms rows_before
#print axioms rebuild_succeeds
#print axioms rows_after
#print axioms rebuild_not_preserved
#print axioms strict_rebuild_fails
#print axioms strict_copy_stores_nothing
#print axioms rebuildThenRows_is_the_rebuild_and_the_query

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
/-- Replay the query before the rebuild, the rebuild with the query after it, and the copy into a STRICT table,
on the database of the fixture. -/
elab "report_rebuild_affinity_replays" : command => Command.liftTermElabM do
  emitReplay "zip-before" (← Replay.scriptReport (mkConst ``addresses) (mkConst ``zipRows))
  emitReplay "zip-after" (← Replay.scriptReport (mkConst ``addresses) (mkConst ``rebuildThenRows))
  emitReplay "strict-copy" (← Replay.scriptReport (mkConst ``addresses) (mkConst ``strictCopy))

report_rebuild_affinity_replays

end RebuildAffinity
