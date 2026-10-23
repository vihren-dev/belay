import Belay.Sqlite.Script
import Belay.Sqlite.Database

set_option doc.verso true

/-! The surface's runs (ADR 0017, D3, amended 2026-10-22; ADR 0022, D5, amended): {lit}`db.run s`
runs the statements of script {lit}`s` one at a time, as an application sends them, with the
model's run that resolves each statement when it runs and continues after an error. The run
decides {lit}`Database.Valid` for the database at its end, and the decision is the proof of the
{lit}`Database` that it gives. {lit}`Database.Raw.run` runs a script on a plain database
without the check. {lit}`RunLaws.lean` states how runs compose. -/

namespace Belay.Sqlite

export Belay.Sqlite.Model (Output Output.rows Output.done Output.error Output.oneOf Output.unmodeled
  Output.endsRun Output.isError Connection ScriptRun ScriptRun.ended ScriptRun.andThen)

/-- The context in which the surface resolves the statements of a run: the pinned profile
({name}`Profile.pinned`), with statements that run. -/
def runContext : Belay.Sqlite.Model.ResolveContext := { profile := Profile.pinned, mode := .execution }

/-- The model's run of the script on the connection, each statement with its values
({name}`Belay.Sqlite.Model.runScriptFrom`), from the first statement, without a clock and
without a check of the database at its end. A statement that reads the clock ends the run. -/
def Script.runOn (connection : Connection) (script : Script) : ScriptRun :=
  Belay.Sqlite.Model.runScriptFrom runContext none 0 connection script.statements

/-- The idle connection to the plain database: no open transaction, foreign keys off, as a new
SQLite connection, and the clock assignment of 0 at every position, which the run carries
without a change. -/
def Database.Raw.connection (raw : Database.Raw) : Connection := { state := { database := raw } }

/-- Run the script on the plain database ({name}`Script.runOn` of
{name}`Database.Raw.connection`): the model's result that the run reached, without the check
that the database at its end is valid. -/
def Database.Raw.run (raw : Database.Raw) (script : Script) : ScriptRun := script.runOn raw.connection

/-- The result of a run. -/
structure Run where
  /-- One output for each statement that ran, in order; the last is {name}`Output.unmodeled`
  when the run ended early, or when the database at its end is not valid. -/
  outputs : List Output
  /-- The database that the connection sees at the end, or {name}`Run.start` when the
  database at the end is not valid. -/
  db : Database
  /-- The database at the start of the run. -/
  start : Database
  /-- The database at {lit}`BEGIN` of a transaction that is open at the end, or
  {lean}`(none : Option Database.Raw)` when no transaction is open. -/
  transaction : Option Database.Raw
  /-- Whether {lit}`PRAGMA foreign_keys` is on at the end. -/
  foreignKeys : Bool

/-- The reason of the output that ends a run whose database at its end is not valid. -/
def invalidReason : String :=
  "the database at the end of the run is not valid: a NOT NULL, CHECK, type, key or rowid " ++
    "constraint fails; the run keeps the database at its start. To see the database that the " ++
    "run reached, run the script with Database.Raw.run on db.raw"

/-- The run that the model's result gives from the start database, with the check: when the
database at the end is valid ({name}`Database.Valid`), the decision is the proof of the
{name}`Database` that the run gives; otherwise the outputs end with {name}`Output.unmodeled`,
with {name}`invalidReason` unless the model's run ended already, and the run keeps the start
database, idle with foreign keys off. -/
def Run.checked (start : Database) (result : ScriptRun) : Run :=
  if valid : result.connection.state.database.Valid Profile.pinned then
    { outputs := result.outputs, db := ⟨_, valid⟩, start, transaction := result.connection.state.snapshot,
      foreignKeys := result.connection.foreignKeys }
  else
    { outputs := if result.ended then result.outputs else result.outputs ++ [.unmodeled invalidReason],
      db := start, start, transaction := none, foreignKeys := false }

/-- Run the script on the database, one statement at a time, with the check of the database at
the end ({name}`Run.checked` of {name}`Database.Raw.run`). For example, an UPDATE that changes
one row, then a query, give {lit}`[done 1, rows [[1, 10]]]`. -/
def Database.run (db : Database) (script : Script) : Run := Run.checked db (db.raw.run script)

/-- Run the script on the database up to and including its first statement that fails
({name}`Output.isError`), as {lit}`sqlite3_exec` does: the run of the statements before the
first error and of the failed statement, or of the whole script without an error. -/
def Script.runUntilError (script : Script) (db : Database) : Run :=
  match (db.run script).outputs.findIdx? Output.isError with
  | some position => db.run ⟨script.statements.take (position + 1)⟩
  | none => db.run script

end Belay.Sqlite
