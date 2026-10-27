import Belay.Sqlite.ProgramSuccess
import Belay.Sqlite.RunLaws
import Belay.Sqlite.ProgramEnvLaws

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite Belay.Sqlite.Model

/-- For every script, database and environment, its public output list equals the model's
output list from the environment's clock and counters. Proof sketch: the program is
{name}`send`, whose run is the model's script run; validity leaves its outputs unchanged. -/
theorem Script.run_outputs (script : Script) (db : Database) (env : Env) :
    (db.run script env).outputs =
      (runScriptFrom runContext env.clock 0 (db.raw.connection env.counters) script.statements).outputs := by
  change ((send script).run db env).outputs = _
  rw [Sql.run_outputs, send, Sql.runFrom_send]
  rfl

/-- For every list of statements, clock, index and connection, if sending the statements succeeds on
every branch, the model's own run of the statements has no error or ending output. The converse holds
for statements that have one execution each ({lit}`Sql.succeedsFrom_sendStatements`). Proof sketch:
induction on the statements; the model's own execution is one of the executions of the first statement, so
it succeeds, and mapping the accumulated outputs leaves success unchanged. -/
theorem Sql.allOk_of_succeedsFrom_send (statements : List (Syntax.Statement × List Value)) :
    ∀ (clock : Option Clock) (index : Nat) (connection : Connection),
      (sendStatements statements).SucceedsFrom clock index connection →
        (runScriptFrom runContext clock index connection statements).outputs.allOk = true := by
  induction statements with
  | nil => intro clock index connection _; simp [runScriptFrom, List.allOk]
  | cons head tail later =>
    rcases head with ⟨statement, values⟩
    intro clock index connection success
    cases step : runScriptStep runContext clock index connection statement values with
    | ended reason => simp [sendStatements, Sql.SucceedsFrom, step] at success
    | continued output next others =>
      have quiet := (runScriptStep_continued step).2
      simp only [sendStatements, Sql.SucceedsFrom, step] at success
      have own := success { output, next } (by simp [RunStep.executions])
      unfold Sql.ExecutionSucceeds at own
      have rest := later clock (index + 1) next
        ((Sql.succeedsFrom_map _ _ _ _ _).mp own.2.1)
      simp only [runScriptFrom, step]
      cases output <;> simp_all [List.allOk, Output.isError, Output.endsRun]

/-- For every list of statements with one execution each ({name}`ScriptConditionsWith` for statements that
are no INSERT from a query without rules), clock, index and connection, sending the statements
succeeds on every branch exactly when their model run has no error or ending output.
Scripts do not choose later statements from earlier results. Proof sketch: induction on
the statements; mapping the accumulated outputs leaves success unchanged, so all alternative
continuations require the same remaining script. The direction from success to the model run holds without
the condition ({name}`Sql.allOk_of_succeedsFrom_send`). -/
theorem Sql.succeedsFrom_sendStatements (statements : List (Syntax.Statement × List Value)) :
    ∀ (clock : Option Clock) (index : Nat) (connection : Connection),
      ScriptConditionsWith (fun resolved _ => resolved.fromQuery = false) runContext clock index connection statements →
      ((sendStatements statements).SucceedsFrom clock index connection ↔
        (runScriptFrom runContext clock index connection statements).outputs.allOk = true) := by
  induction statements with
  | nil => intro clock index connection _; simp [sendStatements, Sql.SucceedsFrom, runScriptFrom, List.allOk]
  | cons head tail later =>
    rcases head with ⟨statement, values⟩
    intro clock index connection single
    simp only [sendStatements, runScriptFrom]
    cases step : runScriptStep runContext clock index connection statement values with
    | ended reason => simp [Sql.SucceedsFrom, step, List.allOk, Output.isError, Output.endsRun]
    | continued output next others =>
      have quiet := (runScriptStep_continued step).2
      obtain ⟨noOthers, restSingle⟩ := ScriptConditionsWith.single_step single step
      rw [Sql.succeedsFrom_continued step noOthers]
      unfold Sql.ExecutionSucceeds
      simp only [Sql.succeedsFrom_map, later clock (index + 1) next restSingle]
      cases output <;> simp_all [List.allOk, Output.isError, Output.endsRun]

/-- For every script and database predicate, when no statement of the script is written as INSERT from a query,
the script succeeds exactly when its public
run has no error or ending output for every database satisfying the predicate and every
complete environment. Both sides hold vacuously when no database satisfies the predicate.
Proof sketch: {name}`Sql.succeedsFrom_sendStatements` removes the unused result branches, with the condition of
one execution from {name}`ScriptConditionsWith.of_not_insertSelect`;
{name}`Sql.runFrom_send` and {name}`Sql.run_outputs` identify the public outputs. -/
theorem Succeeds.script_iff (script : Script) (predicate : Database → Prop)
    (single : ∀ entry ∈ script.statements, entry.1.isInsertSelect = false) :
    Succeeds script predicate ↔
      ∀ db, predicate db → ∀ env : Env, env.Complete → (db.run script env).outputs.allOk = true := by
  simp only [Succeeds, Database.run, Sql.run_outputs]
  change (∀ db, predicate db → ∀ env : Env, env.Complete →
    (sendStatements script.statements).SucceedsFrom env.clock 0 (db.raw.connection env.counters)) ↔
    (∀ db, predicate db → ∀ env : Env, env.Complete →
      ((sendStatements script.statements).runFrom env.clock 0 (db.raw.connection env.counters)).outputs.allOk = true)
  simp only [Sql.succeedsFrom_sendStatements _ _ _ _
      (ScriptConditionsWith.of_not_insertSelect runContext _ _ _ _ single),
    Sql.runFrom_send, SqlRun.ofScript]

/-- For every script, database and environment, if all default-run outputs succeed, the
outputs also succeed in that environment. Proof sketch: no successful output ends at a
missing clock or counter, so {name}`Script.run_env` identifies the two runs. -/
theorem Script.allOk_env {script : Script} {db : Database}
    (success : (db.run script).outputs.allOk = true) (env : Env) :
    (db.run script env).outputs.allOk = true := by
  have quiet := fun output member => ((List.allOk_iff _).mp success output member).2
  have noClock : Output.unmodeled clockUnmodeled ∉ (db.run script).outputs := by
    intro member
    have := quiet _ member
    simp [Output.endsRun] at this
  have known : ∀ output ∈ (db.run script).outputs, output.endsAtUnknownCounter = false := by
    intro output member
    cases found : output.endsAtUnknownCounter
    · rfl
    · have ends := Output.endsRun_of_endsAtUnknownCounter found
      rw [quiet output member] at ends
      cases ends
  rw [Script.run_env script db env noClock known]
  exact success

/-- For every script and predicate, when no statement of the script is written as INSERT from a query, if every
database satisfying the predicate has a
successful default run, the script succeeds. This sufficient condition need not hold for a
script that reads the clock. Proof sketch: {name}`Script.allOk_env` gives every complete
environment, and {name}`Succeeds.script_iff` gives success. -/
theorem Succeeds.of_default {script : Script} {predicate : Database → Prop}
    (single : ∀ entry ∈ script.statements, entry.1.isInsertSelect = false)
    (success : ∀ db, predicate db → (db.run script).outputs.allOk = true) : Succeeds script predicate :=
  (Succeeds.script_iff script predicate single).mpr fun db holds env _ => Script.allOk_env (success db holds) env

/-- For every database and two scripts, under the hypotheses of {name}`Script.run_append`,
their concatenation's public run has no error or ending output exactly when both the first
run and the second run on its resulting database have none. These are default-environment
runs; the hypotheses exclude the counter-reset difference between the two connections.
Proof sketch: {name}`Script.run_append` concatenates the output lists, and checking all
outputs of a concatenation checks each list. -/
theorem Script.allOk_append (db : Database) (first second : Script)
    (outside : (db.run first).transaction = none)
    (setting : (db.run first).foreignKeys = false)
    (recursive : (db.run first).recursiveTriggers = false)
    (modeled : ∀ output ∈ (db.run first).outputs, output.endsRun = false)
    (modeledLater : ∀ output ∈ ((db.run first).db.run second).outputs, output.endsRun = false) :
    (db.run (first ++ second)).outputs.allOk = true ↔
      (db.run first).outputs.allOk = true ∧ ((db.run first).db.run second).outputs.allOk = true := by
  rw [Script.run_append db first second outside setting recursive modeled modeledLater]
  simp only [List.allOk, List.all_append, Bool.and_eq_true]

end Belay.Sqlite
