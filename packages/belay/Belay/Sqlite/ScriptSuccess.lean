import Belay.Sqlite.ProgramSuccess
import Belay.Sqlite.RunLaws

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite Belay.Sqlite.Model

/-- For every list of statements, clock, index and connection, sending the statements
succeeds on every branch exactly when their model run has no error or ending output.
Scripts do not choose later statements from earlier results. Proof sketch: induction on
the statements; mapping the accumulated outputs leaves success unchanged, so all alternative
continuations require the same remaining script. -/
theorem Sql.succeedsFrom_sendStatements (statements : List (Syntax.Statement × List Value)) :
    ∀ (clock : Option Clock) (index : Nat) (connection : Connection),
      (sendStatements statements).SucceedsFrom clock index connection ↔
        (runScriptFrom runContext clock index connection statements).outputs.allOk = true := by
  induction statements with
  | nil => intro clock index connection; simp [sendStatements, Sql.SucceedsFrom, runScriptFrom, List.allOk]
  | cons head tail later =>
    rcases head with ⟨statement, values⟩
    intro clock index connection
    simp only [sendStatements, Sql.SucceedsFrom, runScriptFrom]
    cases step : runScriptStep runContext clock index connection statement values with
    | ended reason => simp [List.allOk, Output.isError, Output.endsRun]
    | continued output next =>
      have quiet := (runScriptStep_continued step).2
      simp only [Sql.succeedsFrom_map, later]
      cases output <;> simp_all [List.allOk, Output.isError, Output.endsRun]

/-- For every script and database predicate, the script succeeds exactly when its public
run has no error or ending output for every database satisfying the predicate and every
complete environment. Both sides hold vacuously when no database satisfies the predicate.
Proof sketch: {name}`Sql.succeedsFrom_sendStatements` removes the unused result branches;
{name}`Sql.runFrom_send` and {name}`Sql.run_outputs` identify the public outputs. -/
theorem Succeeds.script_iff (script : Script) (predicate : Database → Prop) :
    Succeeds script predicate ↔
      ∀ db, predicate db → ∀ env : Env, env.Complete → (db.run script env).outputs.allOk = true := by
  simp only [Succeeds, Database.run, Sql.run_outputs]
  change (∀ db, predicate db → ∀ env : Env, env.Complete →
    (sendStatements script.statements).SucceedsFrom env.clock 0 (db.raw.connection env.counters)) ↔
    (∀ db, predicate db → ∀ env : Env, env.Complete →
      ((sendStatements script.statements).runFrom env.clock 0 (db.raw.connection env.counters)).outputs.allOk = true)
  simp only [Sql.succeedsFrom_sendStatements, Sql.runFrom_send, SqlRun.ofScript]

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
