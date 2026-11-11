import Belay

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Checks of the run observations of ADR 0027 D2 ({lit}`Run.returnsResult`, {lit}`Run.returnsRows` and
{lit}`Run.returnsError`) and of the claims {lit}`Holds`, {lit}`Empty` and {lit}`Fails`, which are
abbreviations of them. The probes run the model on a concrete database for each output shape: rows, a
choice of results, an error, an unmodeled stop, an empty choice and more than one output. -/

namespace SelectRunObservations
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

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

#print axioms rows_observed
#print axioms choice_observed
#print axioms error_observed
#print axioms unmodeled_observed
#print axioms no_single_result
#print axioms bridge_instance

end SelectRunObservations
