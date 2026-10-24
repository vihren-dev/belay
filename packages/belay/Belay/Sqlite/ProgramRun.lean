import Belay.Sqlite.Program
import Belay.Sqlite.Env
import Belay.Sqlite.Run

set_option doc.verso true

/-! The runs of programs and scripts on a database (ADR 0017, D1 and D3; ADR 0022, D5, amended):
{lit}`Sql.run p db` sends each statement of program {lit}`p` as one statement of the model's
run, at the next index, on the connection that the earlier statements left, and gives the
statement's output to the rest of the program. A statement whose output is
{lit}`Output.unmodeled` ends the program. The validity theorem
for the run supplies the proof of the {lit}`Database` that it gives. {lit}`db.run`
takes a program or a script; a script is the program {lit}`send s`. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- What the model's run of a program reached:
the outputs and the connection, as for a script, and the program's value, which is none when the
run ended with {name}`Output.unmodeled`. -/
structure SqlRun (α : Type) extends ScriptRun where
  /-- The program's value, or none when a statement ended the run. -/
  value : Option α

/-- Run the program from a zero-based index on the connection, with an optional clock: each
statement runs as one step of the model's run ({name}`Belay.Sqlite.Model.runScriptStep`); its
output goes to the rest of the program, which runs from the next index on the connection after
the statement. A statement that ends the run gives {name}`Output.unmodeled` with the reason, and
the rest of the program does not run. -/
def Sql.runFrom {α : Type} (clock : Option Clock) (index : Nat) (connection : Connection) : Sql α → SqlRun α
  | .pure value => { outputs := [], connection, value := some value }
  | .exec statement values rest =>
    match runScriptStep runContext clock index connection statement values with
    | .ended reason => { outputs := [.unmodeled reason], connection, value := none }
    | .continued output next =>
      let later := (rest output).runFrom clock (index + 1) next
      { later with outputs := output :: later.outputs }

/-- For every program, clock, index and connection: if the state of the connection satisfies
{name}`Belay.Sqlite.Model.SqlState.Holds` for {name}`Database.Valid` under the pinned profile (its database, and
its snapshot when a transaction is open), the state of the connection at the end of
{name}`Sql.runFrom` satisfies it. It holds for every program of the surface, whatever its statements: the
validity proof of the final database follows from a valid start. Proof sketch: induction
over the program; a statement that ends the run keeps the connection, and a statement that continues is
one step of the model's run, which keeps the database valid
({name}`Belay.Sqlite.Model.runScriptStep_valid`, for the context {name}`runContext`, in execution mode with the
limits of the pinned profile). -/
theorem Sql.runFrom_valid {α : Type} (clock : Option Clock) (program : Sql α) :
    ∀ (index : Nat) {connection : Connection}, connection.state.Holds (Database.Valid Profile.pinned) →
      (program.runFrom clock index connection).connection.state.Holds (Database.Valid Profile.pinned) := by
  induction program with
  | pure value => exact fun _ _ holds => holds
  | exec statement values rest hypothesis =>
    intro index connection holds
    unfold Sql.runFrom
    have step := fun output next => runScriptStep_valid (profile := Profile.pinned) runContext clock index statement values
      rfl rfl holds (output := output) (next := next)
    cases found : runScriptStep runContext clock index connection statement values with
    | ended reason => exact holds
    | continued output next => exact hypothesis output (index + 1) (step output next found)

/-- For every program, database and environment: the database of the connection at the end of the run of
{lit}`Sql.run` is valid under the pinned profile. This proof supplies the final bundled database.
Proof sketch:
{name}`Sql.runFrom_valid` from the idle connection, whose database is the valid database. -/
theorem Sql.runFrom_database_valid {α : Type} (program : Sql α) (db : Database) (env : Env) :
    (program.runFrom env.clock 0 (db.raw.connection env.counters)).connection.state.database.Valid Profile.pinned :=
  (Sql.runFrom_valid env.clock program 0 ⟨db.valid, fun _ same => by simp [Database.Raw.connection] at same⟩).1

/-- The result of a run of a program. -/
structure Run (α : Type) where
  /-- The program's value: none when a statement ended the run with {name}`Output.unmodeled`. -/
  value : Option α
  /-- One output for each statement that ran, in order; the last is {name}`Output.unmodeled`
  when the run ended early. -/
  outputs : List Output
  /-- The valid database that the connection sees at the end. -/
  db : Database
  /-- The database at the start of the run. -/
  start : Database
  /-- The database at {lit}`BEGIN` of a transaction that is open at the end, or
  {lean}`(none : Option Database.Raw)` when no transaction is open. -/
  transaction : Option Database.Raw
  /-- Whether {lit}`PRAGMA foreign_keys` is on at the end. -/
  foreignKeys : Bool
  /-- Whether {lit}`PRAGMA recursive_triggers` is on at the end. -/
  recursiveTriggers : Bool

/-- Bundle a model result whose final database is valid. The supplied proof certifies the
result's database; its value, outputs, transaction and settings are preserved. Use the
valid-run theorem when constructing this result from a program. -/
def Run.ofValid {α : Type} (start : Database) (result : SqlRun α)
    (valid : result.connection.state.database.Valid Profile.pinned) : Run α :=
  { value := result.value, outputs := result.outputs, db := ⟨_, valid⟩, start,
    transaction := result.connection.state.snapshot, foreignKeys := result.connection.foreignKeys,
    recursiveTriggers := result.connection.recursiveTriggers }

/-- Run the program on the database in the environment, from the idle connection to the
database, from the counters of the environment. The final database carries the proof from
{name}`Sql.runFrom_database_valid`; the result uses {name}`Run.ofValid`. Use {name}`Env.default`, the value when
{lit}`env` is not given, when no statement reads the clock or a counter that the program does not
set first. -/
def Sql.run {α : Type} (program : Sql α) (db : Database) (env : Env := Env.default) : Run α :=
  Run.ofValid db (program.runFrom env.clock 0 (db.raw.connection env.counters))
    (Sql.runFrom_database_valid program db env)

/-- The things that {lit}`db.run` runs: a program of type {lit}`Sql α` itself (the default
instance, so that a {lit}`do` block is a program), and a script, which is the program
{name}`send` of it. -/
class Runnable (σ : Type) (α : outParam Type) where
  /-- The program of the thing. -/
  toSql : σ → Sql α

/-- A program is the program that {lit}`db.run` runs. -/
@[default_instance] instance {α : Type} : Runnable (Sql α) α := ⟨id⟩

/-- A script is the program that sends its statements ({name}`send`). -/
instance : Runnable Script (List Output) := ⟨send⟩

/-- Run the program or the script on the database in the environment ({name}`Sql.run`), with
the database first, so that a {lit}`do` block needs no parentheses: {lit}`db.run do ...`.
For example, an UPDATE that changes one row, then a query, give the outputs
{lit}`[done 1, rows [[1, 10]]]`. -/
def Database.run {σ α : Type} [Runnable σ α] (db : Database) (program : σ) (env : Env := Env.default) : Run α :=
  (Runnable.toSql program).run db env

/-- Run the script on the database up to and including its first statement that fails
({name}`Output.isError`), as {lit}`sqlite3_exec` does: the run of the statements before the
first error and of the failed statement, or of the whole script without an error. -/
def Script.runUntilError (script : Script) (db : Database) : Run (List Output) :=
  match (db.run script).outputs.findIdx? Output.isError with
  | some position => db.run (⟨script.statements.take (position + 1)⟩ : Script)
  | none => db.run script

end Belay.Sqlite
