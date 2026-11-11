import Belay.Sqlite.Programs.Scripts.ScriptSuccess
import Belay.Sqlite.Programs.Scripts.QueryObservations

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite Belay.Sqlite.Model

/-- For every query script and database, the default run's output list is the singleton
list of its query observation. Proof sketch: a query has one statement, and either its
ending step or its continuing step contributes exactly one output. -/
theorem Script.query_outputs {script : Script} (query : script.isQuery = true) (db : Database) :
    (db.run script).outputs = (script.outputOn db).toList := by
  obtain ⟨statement, values, one⟩ := Script.singleton_of_isQuery query
  rw [Script.run_outputs]
  unfold Script.outputOn Database.Raw.run Script.runOn
  rw [one]
  cases step : runScriptStep runContext none 0 db.raw.connection statement values <;>
    simp [Env.default, runScriptFrom, step]

/-- For every query and database, its default run succeeds exactly when {name}`Fails` is
false and its query output does not end the run. The ending-output condition excludes
unmodeled queries, including clock reads in the default environment. Proof sketch: the
query has one output; inspect its five possible constructors. -/
theorem Script.query_allOk_iff {script : Script} (query : script.isQuery = true) (db : Database) :
    (db.run script).outputs.allOk = true ↔
      ¬ Fails script db query ∧ (script.outputOn db).any Output.endsRun = false := by
  rw [Script.query_outputs query db, Fails, Script.returnsError_iff_outputOn query]
  cases found : script.outputOn db with
  | none => simp [List.allOk]
  | some output => cases output <;> simp [List.allOk, Output.returnsError, Output.isError, Output.endsRun]

/-- For every query and predicate, if every database satisfying the predicate has neither a
query error nor an ending query output in the default environment, the query succeeds.
Proof sketch: {name}`Script.query_allOk_iff` supplies the default output check and
{name}`Succeeds.of_default` extends it to every complete environment. -/
theorem Succeeds.of_query {script : Script} {predicate : Database → Prop} (query : script.isQuery = true)
    (success : ∀ db, predicate db → ¬ Fails script db query ∧
      (script.outputOn db).any Output.endsRun = false) : Succeeds script predicate :=
  Succeeds.of_default (Script.noInsertSelect_of_isQuery query) fun db holds =>
    (Script.query_allOk_iff query db).mpr (success db holds)

/-- For every query and predicate, if the query holds on every database satisfying the
predicate, it succeeds. Proof sketch: a row-bearing output is neither an error nor an
ending output; {name}`Succeeds.of_query` then covers every environment. -/
theorem Succeeds.of_holds {script : Script} {predicate : Database → Prop} {query : script.isQuery = true}
    (holds : ∀ db, predicate db → Holds script db query) : Succeeds script predicate := by
  apply Succeeds.of_query query
  intro db condition
  obtain ⟨output, found, rows⟩ := (Script.returnsResult_iff_outputOn query db _).mp (holds db condition)
  rw [Fails, Script.returnsError_of_outputOn query found]
  cases output <;> simp_all [Output.returnsResult, Output.returnsError, Output.endsRun]

end Belay.Sqlite
