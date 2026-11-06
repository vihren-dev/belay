import Belay.Sqlite.RunResults
import Belay.Sqlite.ProgramQueries
import Belay.Sqlite.ProgramLaws
import Belay.Sqlite.Model.ScriptRunIndex

set_option doc.verso true

/-! The successful-result and error observations of the run of one statement (ADR 0027, D2): the
run of {lit}`query s` or of the script {lit}`s` itself, for a script of one statement, returns a
result or an error exactly when the output of the step of that statement does. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every script of one statement, database, environment and property {lit}`Q`: the run of the
program {name}`query` of the script returns a result with {lit}`Q` ({name}`Run.returnsResult`) exactly
when the output of the step of the statement on the new connection returns one. The step reads the
clock and the counters of the environment. Proof sketch: a step that ends the run gives the value
none; one that continues gives its output as the one output. -/
theorem Run.query_returnsResult_iff {script : Script} (one : script.statements.length = 1) (db : Database) (env : Env)
    (property : List (List Value) → Prop) :
    (db.run (query script one) env).returnsResult property ↔
      (runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
        (script.statements[0]'(by rw [one]; exact Nat.one_pos)).1
        (script.statements[0]'(by rw [one]; exact Nat.one_pos)).2).output.returnsResult property := by
  change ((query script one).run db env).returnsResult property ↔ _
  unfold Sql.run Run.ofValid query
  generalize script.statements[0]'(by rw [one]; exact Nat.one_pos) = entry
  obtain ⟨statement, values⟩ := entry
  cases step : runScriptStep runContext env.clock 0 (db.raw.connection env.counters) statement values with
  | ended reason => simp [Run.returnsResult, Sql.runFrom, step, RunStep.output, Output.returnsResult]
  | continued actual next others => simp [Run.returnsResult, Sql.runFrom, step, RunStep.output]

/-- For every script of one statement, database, environment and property {lit}`E` of a result code:
the run of the program {name}`query` of the script returns an error with {lit}`E`
({name}`Run.returnsError`) exactly when the output of the step of the statement on the new connection
is such an error. Proof sketch: as {name}`Run.query_returnsResult_iff`. -/
theorem Run.query_returnsError_iff {script : Script} (one : script.statements.length = 1) (db : Database) (env : Env)
    (property : Nat → Prop) :
    (db.run (query script one) env).returnsError property ↔
      (runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
        (script.statements[0]'(by rw [one]; exact Nat.one_pos)).1
        (script.statements[0]'(by rw [one]; exact Nat.one_pos)).2).output.returnsError property := by
  change ((query script one).run db env).returnsError property ↔ _
  unfold Sql.run Run.ofValid query
  generalize script.statements[0]'(by rw [one]; exact Nat.one_pos) = entry
  obtain ⟨statement, values⟩ := entry
  cases step : runScriptStep runContext env.clock 0 (db.raw.connection env.counters) statement values with
  | ended reason => simp [Run.returnsError, Sql.runFrom, step, RunStep.output, Output.returnsError]
  | continued actual next others => simp [Run.returnsError, Sql.runFrom, step, RunStep.output]

/-- For every script of one statement, database, environment and property {lit}`Q` of a result: the
run of the script ({name}`send`) returns a result with {lit}`Q` exactly when the output of the step of
the statement on the new connection returns one. Proof sketch: the run of {name}`send` is the model's
run of the statements ({name}`Sql.runFrom_send`); a step that ends the run gives the value none. -/
theorem Run.send_returnsResult_iff {script : Script} (one : script.statements.length = 1) (db : Database) (env : Env)
    (property : List (List Value) → Prop) :
    (db.run script env).returnsResult property ↔
      (runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
        (script.statements[0]'(by rw [one]; exact Nat.one_pos)).1
        (script.statements[0]'(by rw [one]; exact Nat.one_pos)).2).output.returnsResult property := by
  obtain ⟨⟨statement, values⟩, same⟩ := List.length_eq_one_iff.mp one
  obtain rfl : script = ⟨[(statement, values)]⟩ := by cases script; simp_all
  change ((send ⟨[(statement, values)]⟩).run db env).returnsResult property ↔ _
  rw [Run.returnsResult_iff]
  simp only [Sql.run, Run.ofValid, send, Sql.runFrom_send, List.getElem_cons_zero]
  cases step : runScriptStep runContext env.clock 0 (db.raw.connection env.counters) statement values with
  | ended reason =>
    simp [SqlRun.ofScript, runScriptFrom, step, ScriptRun.ended, Output.endsRun, RunStep.output,
      Output.returnsResult]
  | continued actual next others =>
    have ends := (runScriptStep_continued step).2
    simp [SqlRun.ofScript, runScriptFrom, step, ScriptRun.ended, ends, RunStep.output]

/-- For every script of one statement, database, environment and property {lit}`E` of a result code:
the run of the script returns an error with {lit}`E` exactly when the output of the step of the
statement on the new connection is such an error. Proof sketch: as {name}`Run.send_returnsResult_iff`. -/
theorem Run.send_returnsError_iff {script : Script} (one : script.statements.length = 1) (db : Database) (env : Env)
    (property : Nat → Prop) :
    (db.run script env).returnsError property ↔
      (runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
        (script.statements[0]'(by rw [one]; exact Nat.one_pos)).1
        (script.statements[0]'(by rw [one]; exact Nat.one_pos)).2).output.returnsError property := by
  obtain ⟨⟨statement, values⟩, same⟩ := List.length_eq_one_iff.mp one
  obtain rfl : script = ⟨[(statement, values)]⟩ := by cases script; simp_all
  change ((send ⟨[(statement, values)]⟩).run db env).returnsError property ↔ _
  rw [Run.returnsError_iff]
  simp only [Sql.run, Run.ofValid, send, Sql.runFrom_send, List.getElem_cons_zero]
  cases step : runScriptStep runContext env.clock 0 (db.raw.connection env.counters) statement values with
  | ended reason =>
    simp [SqlRun.ofScript, runScriptFrom, step, ScriptRun.ended, Output.endsRun, RunStep.output,
      Output.returnsError]
  | continued actual next others =>
    have ends := (runScriptStep_continued step).2
    simp [SqlRun.ofScript, runScriptFrom, step, ScriptRun.ended, ends, RunStep.output]

end Belay.Sqlite
