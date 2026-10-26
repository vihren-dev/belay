import Belay.Sqlite.ProgramRun

set_option doc.verso true

/-! The laws of the runs of programs ({lit}`ProgramRun.lean`): the run of {lit}`send s` is the
model's run of script {lit}`s`, with the same outputs and connection, so the laws of the runs of
scripts ({lit}`RunLaws.lean`) hold for {lit}`db.run s`; and a clock does not change a run in
which no statement reads it ({lit}`Sql.runFrom_env`). -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- The result of the program {name}`send` from the model's run of its script: the same outputs
and connection, and the value {lit}`some` of the outputs, or none when the run ended
({name}`ScriptRun.ended`). -/
def SqlRun.ofScript (run : ScriptRun) : SqlRun (List Output) :=
  { toScriptRun := run, value := if run.ended then none else some run.outputs }

/-- For every run of a script, the outputs and the connection of {name}`SqlRun.ofScript` of it
are those of the run. Proof sketch: by the definition. -/
@[simp] theorem SqlRun.ofScript_toScriptRun (run : ScriptRun) : (SqlRun.ofScript run).toScriptRun = run := rfl

/-- For every function, program, optional clock, index and connection: the run of the program
with the function applied to its value ({name}`Sql.map`) has the outputs and the connection of
the run of the program, and its value is the function applied to the value of that run. Proof
sketch: induction on the program; {name}`Sql.map` changes only the value of
{name}`Sql.pure`, and each statement takes the same step in both runs. -/
theorem Sql.runFrom_map {α β : Type} (function : α → β) (program : Sql α) :
    ∀ (clock : Option Clock) (index : Nat) (connection : Connection),
      (program.map function).runFrom clock index connection =
        { (program.runFrom clock index connection) with
          value := (program.runFrom clock index connection).value.map function } := by
  induction program with
  | pure value => intro clock index connection; rfl
  | exec statement values rest later =>
    intro clock index connection
    simp only [Sql.map, Sql.runFrom]
    split
    · rfl
    · rw [later]

/-- For every optional clock, index, connection and statements with values: the run of the
program that sends the statements ({name}`sendStatements`) is the model's run of the statements
({name}`Belay.Sqlite.Model.runScriptFrom`, {name}`SqlRun.ofScript`): the same outputs and
connection, and the value {lit}`some` of the outputs when the run did not end. Proof sketch:
induction on the statements; both runs take the same step for each statement, and the output
of a step that continues does not end a run
({name}`Belay.Sqlite.Model.runScriptStep_continued`). -/
theorem Sql.runFrom_send (clock : Option Clock) :
    ∀ (index : Nat) (connection : Connection) (statements : List (Syntax.Statement × List Value)),
      (sendStatements statements).runFrom clock index connection =
        SqlRun.ofScript (runScriptFrom runContext clock index connection statements)
  | _, _, [] => rfl
  | index, connection, (statement, values) :: rest => by
    simp only [sendStatements, Sql.runFrom, runScriptFrom]
    cases step : runScriptStep runContext clock index connection statement values with
    | ended reason => simp [SqlRun.ofScript, ScriptRun.ended, Output.endsRun]
    | continued output next =>
      simp only [Sql.runFrom_map, Sql.runFrom_send clock (index + 1) next rest, SqlRun.ofScript]
      have quiet := (runScriptStep_continued step).2
      cases ended : (runScriptFrom runContext clock (index + 1) next rest).ended <;>
        simp_all [ScriptRun.ended]

/-- For every database, script and environment, the final database of the model's script
run is valid under the pinned profile. Proof sketch: the general model run theorem starts
from the valid database and an idle transaction. -/
theorem Script.run_database_valid (script : Script) (db : Database) (env : Env) :
    (runScriptFrom runContext env.clock 0 (db.raw.connection env.counters) script.statements).connection.state.database.Valid
      Profile.pinned :=
  (runScriptFrom_valid (profile := Profile.pinned) runContext env.clock 0
    (connection := db.raw.connection env.counters) script.statements rfl rfl
    ⟨db.valid, fun _ same => by simp [Database.Raw.connection] at same⟩).1

/-- For every database, script and environment, the public script run bundles the model's
script result with its validity proof, preserving every field. Proof sketch:
{name}`Sql.runFrom_send` identifies the results; proof irrelevance identifies their validity proofs. -/
theorem Database.run_script (db : Database) (script : Script) (env : Env) :
    db.run script env = Run.ofValid db
      (SqlRun.ofScript (runScriptFrom runContext env.clock 0 (db.raw.connection env.counters) script.statements))
      (Script.run_database_valid script db env) := by
  unfold Database.run Sql.run
  simp only [show Runnable.toSql script = sendStatements script.statements from rfl, Sql.runFrom_send]

/-- For every database and script, its public default run bundles the model's default run
with its validity proof. Proof sketch: specialize {name}`Database.run_script` to the default environment. -/
theorem Database.run_script_default (db : Database) (script : Script) :
    db.run script = Run.ofValid db (SqlRun.ofScript (db.raw.run script))
      (Script.run_database_valid script db Env.default) :=
  Database.run_script db script Env.default

/-- For every program, database and environment, the public run's outputs are exactly the
model run's outputs. Proof sketch: the proof-bearing wrapper preserves the output field. -/
theorem Sql.run_outputs {α : Type} (program : Sql α) (db : Database) (env : Env) :
    (program.run db env).outputs =
      (program.runFrom env.clock 0 (db.raw.connection env.counters)).outputs := rfl

/-- For every program, optional clock, index and connection: if no output of the run without a
clock is {name}`Output.unmodeled` with the reason {name}`clockUnmodeled`, the run with the clock
is the run without a clock. Proof sketch: induction on the program; each step is the step
without a clock ({name}`Belay.Sqlite.Model.runScriptStep_of_ne_clockUnmodeled`), because a step
that ends with {name}`clockUnmodeled` gives that output. -/
theorem Sql.runFrom_env {α : Type} (program : Sql α) (clock : Option Clock) :
    ∀ (index : Nat) (connection : Connection),
      Output.unmodeled clockUnmodeled ∉ (program.runFrom none index connection).outputs →
        program.runFrom clock index connection = program.runFrom none index connection := by
  induction program with
  | pure value => intro index connection _; rfl
  | exec statement values rest later =>
    intro index connection clockFree
    have same : runScriptStep runContext clock index connection statement values =
        runScriptStep runContext none index connection statement values := by
      apply runScriptStep_of_ne_clockUnmodeled
      intro ended
      simp [Sql.runFrom, ended] at clockFree
    simp only [Sql.runFrom, same] at clockFree ⊢
    split
    · rfl
    · rename_i output next step
      rw [step] at clockFree
      rw [later output (index + 1) next (fun found => clockFree (List.mem_cons_of_mem _ found))]

end Belay.Sqlite
