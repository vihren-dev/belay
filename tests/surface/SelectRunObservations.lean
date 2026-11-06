import Belay

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Checks of the run observations of ADR 0027 D2 ({lit}`Run.returnsResult`, {lit}`Run.returnsRows` and
{lit}`Run.returnsError`) and of the claims {lit}`Holds`, {lit}`Empty` and {lit}`Fails` that are now
abbreviations of them. The migration witnesses prove that each claim has the truth value of its earlier
definition over the output of the query on every query script and database; they stay until the last
contract change of the task, then go (ADR 0025 D4). The probes run the model on a concrete database for
each output shape: rows, a choice of results, an error, an unmodeled stop, an empty choice and more than
one output. -/

namespace SelectRunObservations
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- Migration witness: for every query script and database, {name}`Holds` is the earlier definition, a
row in each result of the output of the query. -/
theorem holds_is_earlier (q : Script) (db : Database) (query : q.isQuery = true) :
    Holds q db query ↔ (q.outputOn db).any Output.hasRows = true := by
  obtain ⟨_, _, _, found⟩ := Script.outputOn_isQuery query db
  rw [Holds.iff_of_outputOn found query, found, Option.any_some]

/-- Migration witness: for every query script and database, {name}`Belay.Sqlite.Empty` is the earlier definition, no
row in any result of the output of the query. -/
theorem empty_is_earlier (q : Script) (db : Database) (query : q.isQuery = true) :
    Belay.Sqlite.Empty q db query ↔ (q.outputOn db).any Output.hasNoRows = true := by
  obtain ⟨_, _, _, found⟩ := Script.outputOn_isQuery query db
  rw [Empty.iff_of_outputOn found query, found, Option.any_some]

/-- Migration witness: for every query script and database, {name}`Fails` is the earlier definition, an
error output of the query. -/
theorem fails_is_earlier (q : Script) (db : Database) (query : q.isQuery = true) :
    Fails q db query ↔ (q.outputOn db).any Output.isError = true := by
  obtain ⟨_, _, _, found⟩ := Script.outputOn_isQuery query db
  rw [Fails.iff_of_outputOn found query, found, Option.any_some]

/-- Two non-NULL values, for a query whose one-row window has two permitted results. -/
def sample : Database := db! r"
  CREATE TABLE items(value INTEGER NOT NULL);
  INSERT INTO items VALUES (1), (2);"

/-- Rows: the run of a SELECT of both rows returns a result of two rows, each of one non-NULL cell, and
{name}`Holds` holds. -/
theorem rows_observed :
    (sample.run (sql r"SELECT value FROM items")).returnsResult (·.length = 2) ∧
      (sample.run (sql r"SELECT value FROM items")).returnsRows (fun row => row.length = 1 ∧ ∀ cell ∈ row, cell ≠ .null) ∧
      Holds (sql r"SELECT value FROM items") sample := by
  decide +kernel

/-- A choice of results: the one-row window has two permitted results, so a property of every result
holds and a property of the first result alone does not. -/
theorem choice_observed :
    (sample.run (sql r"SELECT value FROM items LIMIT 1")).returnsResult (·.length = 1) ∧
      ¬ (sample.run (sql r"SELECT value FROM items LIMIT 1")).returnsResult (· = [[.integer 1]]) := by
  decide +kernel

/-- An error: a preparation error returns no result, also not an empty one, and returns the error with
code 1; {name}`Fails` holds and {name}`Belay.Sqlite.Empty` does not. -/
theorem error_observed :
    ¬ (sample.run (sql r"SELECT absent FROM missing")).returnsResult (fun _ => True) ∧
      (sample.run (sql r"SELECT absent FROM missing")).returnsError (· = 1) ∧
      Fails (sql r"SELECT absent FROM missing") sample ∧ ¬ Belay.Sqlite.Empty (sql r"SELECT absent FROM missing") sample := by
  decide +kernel

/-- An unmodeled stop: a read of the clock in the default environment returns neither a result nor an
error. -/
theorem unmodeled_observed :
    ¬ (sample.run (sql r"SELECT CURRENT_TIMESTAMP")).returnsResult (fun _ => True) ∧
      ¬ (sample.run (sql r"SELECT CURRENT_TIMESTAMP")).returnsError (fun _ => True) := by
  decide +kernel

/-- An empty choice and two outputs return no result: an empty list of alternatives does not satisfy a
property vacuously, and a script of two statements has no single observation. -/
theorem no_single_result :
    ¬ (Output.oneOf []).returnsResult (fun _ => True) ∧
      ¬ (sample.run (sql r"SELECT 1; SELECT 2")).returnsResult (fun _ => True) := by
  decide +kernel

/-- The successful-result bridge on a concrete SELECT: for every database, environment and property of
the result, the observation is the success claim of {name}`Sql.check` from the new connection. -/
theorem bridge_instance (db : Database) (env : Env) (property : List (List Value) → Prop) :
    (db.run (query (sql r"SELECT value FROM items")) env).returnsResult property ↔
      (query (sql r"SELECT value FROM items")).check (fun result _ => match result with
        | .ok rows => property rows | .error _ => False) (ExecutionContext.initial db env) :=
  Run.returnsResult_query_iff rfl db env property

#print axioms holds_is_earlier
#print axioms empty_is_earlier
#print axioms fails_is_earlier
#print axioms rows_observed
#print axioms choice_observed
#print axioms error_observed
#print axioms unmodeled_observed
#print axioms no_single_result
#print axioms bridge_instance

end SelectRunObservations
