import Belay

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance cases of the outcomes of a SELECT run under ADR 0027: B01, a modeled error and an
unmodeled stop; B02, a choice of results; B11, a preparation error. The preparation error holds
for every database and environment whose catalog lacks the table, the unmodeled stop for every
database and every environment without a clock; the choice cases run the model on a concrete
database. -/

namespace SelectOutcomeCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- A query of a table {lit}`missing`, which the catalog of the database must not have. -/
def missingQuery : Script := sql r"SELECT absent FROM missing"

/-- The query of the missing table has one statement. -/
theorem missingQuery_one : missingQuery.statements.length = 1 := rfl

/-- A success post: the run returns a result, of any rows. -/
def anyResult (result : Except Nat (List (List Value))) (_ : ExecutionContext) : Prop :=
  match result with | .ok _ => True | .error _ => False

/-- An error post: the run returns an error with code {lit}`expected`. -/
def errorWith (expected : Nat) (result : Except Nat (List (List Value))) (_ : ExecutionContext) : Prop :=
  match result with | .ok _ => False | .error code => code = expected

/-- B11: for every database and environment whose catalog has no table and no view
{lit}`missing`, the query of the missing table

* returns no result with any property, also not an empty one, and
* returns an error with a property exactly when the property holds of code 1, the code of the
  resolution error {lit}`no such table` ({name}`PrepareError.noSuchTable`).

Proof sketch: {name}`resolveStatement_select_missing_table` gives the prepare error, and
{name}`Run.query_prepareError` the observations. -/
theorem missing_table_error (db : Database) (env : Env)
    (missing : db.raw.catalog.findTable (name! "missing") = none)
    (notView : db.raw.catalog.findView (name! "missing") = none) :
    (∀ property, ¬ (db.run (query missingQuery missingQuery_one) env).returnsResult property) ∧
      ∀ code : Nat → Prop, (db.run (query missingQuery missingQuery_one) env).returnsError code ↔ code 1 := by
  have resolved := resolveStatement_select_missing_table runContext (db.raw.connection env.counters).resolveState
    { columns := [.expression (.identifier (name! "absent") .none) none "absent"],
      source := some { table := name! "missing", alias := none }, joins := [], filter := none, groupBy := [],
      orderBy := [], limit := none, offset := none, parent := none, having := none, distinct := false,
      compound := none } _ rfl rfl rfl rfl rfl missing notView rfl rfl
  exact ⟨fun property => (Run.query_prepareError (script := missingQuery) rfl missingQuery_one db env resolved
      property (fun _ => True)).1,
    fun code => (Run.query_prepareError (script := missingQuery) rfl missingQuery_one db env resolved
      (fun _ => True) code).2⟩

/-- B11 and B01 in the form of {name}`Sql.check`: under the premises of
{name}`missing_table_error`, from the new connection of the environment

* the query satisfies the error post with code 1,
* it does not satisfy the error post with the code 19 of a constraint error, and
* it does not satisfy the success post {name}`anyResult`.

Proof sketch: the bridges {name}`Run.returnsError_query_iff` and {name}`Run.returnsResult_query_iff`
turn each post into an observation of {name}`missing_table_error`. -/
theorem missing_table_check (db : Database) (env : Env)
    (missing : db.raw.catalog.findTable (name! "missing") = none)
    (notView : db.raw.catalog.findView (name! "missing") = none) :
    (query missingQuery missingQuery_one).check (errorWith 1) (ExecutionContext.initial db env) ∧
      ¬ (query missingQuery missingQuery_one).check (errorWith 19) (ExecutionContext.initial db env) ∧
      ¬ (query missingQuery missingQuery_one).check anyResult (ExecutionContext.initial db env) := by
  obtain ⟨noResult, error⟩ := missing_table_error db env missing notView
  have errorPost (expected : Nat) :
      (query missingQuery missingQuery_one).check (errorWith expected) (ExecutionContext.initial db env) ↔
        1 = expected :=
    ((error (· = expected)).symm.trans
      (Run.returnsError_query_iff (script := missingQuery) (one := missingQuery_one) rfl db env _)).symm
  refine ⟨(errorPost 1).mpr rfl, fun holds => absurd ((errorPost 19).mp holds) (by decide), fun holds => ?_⟩
  exact noResult (fun _ => True)
    ((Run.returnsResult_query_iff (script := missingQuery) (one := missingQuery_one) rfl db env _).mpr holds)

/-- Two non-NULL values, for a query whose one-row window has two permitted results. -/
def sample : Database := db! r"
  CREATE TABLE items(value INTEGER NOT NULL);
  INSERT INTO items VALUES (1), (2);"

/-- The premises of {name}`missing_table_error` hold on {name}`sample`, which has a table, and on
the empty database. -/
theorem missing_witnesses :
    sample.raw.catalog.findTable (name! "missing") = none ∧ sample.raw.catalog.findView (name! "missing") = none ∧
      Database.empty.raw.catalog.findTable (name! "missing") = none ∧
      Database.empty.raw.catalog.findView (name! "missing") = none := by
  decide +kernel

/-- A read of the clock. -/
def clockQuery : Script := sql r"SELECT CURRENT_TIMESTAMP"

/-- The read of the clock has one statement. -/
theorem clockQuery_one : clockQuery.statements.length = 1 := rfl

/-- B01, an unmodeled stop: for every database and every environment without a clock, the read of
the clock

* satisfies not even the post that always holds,
* returns no result with any property, and
* returns no error with any property.

Proof sketch: {name}`resolveStatement_selectNoFrom` resolves the statement to a query that reads
the clock, so without a clock its step ends the run ({name}`Sql.check_stopped`); the bridges
{name}`Run.returnsResult_query_iff` and {name}`Run.returnsError_query_iff` turn both observations
into checks. -/
theorem unmodeled_stop (db : Database) (env : Env) (noClock : env.clock = none) :
    ¬ (query clockQuery clockQuery_one).check (fun _ _ => True) (ExecutionContext.initial db env) ∧
      (∀ property, ¬ (db.run (query clockQuery clockQuery_one) env).returnsResult property) ∧
      ∀ code, ¬ (db.run (query clockQuery clockQuery_one) env).returnsError code := by
  have resolved := resolveStatement_selectNoFrom runContext (db.raw.connection env.counters).resolveState
    (.currentTime "CURRENT_TIMESTAMP") "CURRENT_TIMESTAMP" none _ _ none rfl rfl rfl rfl (FilterResolves.of_none _ _ _ _)
  have step : runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
      (.select [.expression (.currentTime "CURRENT_TIMESTAMP") none "CURRENT_TIMESTAMP"] none [] none [] [] none none [] none
        false none) [] = .ended clockUnmodeled := by
    rw [noClock]
    unfold runScriptStep runScriptStepWith
    rw [resolved]
    rfl
  have stopped (post : Except Nat (List (List Value)) → ExecutionContext → Prop) :
      ¬ (query clockQuery clockQuery_one).check post (ExecutionContext.initial db env) :=
    Sql.check_stopped (state := ExecutionContext.initial db env) step post
  exact ⟨stopped _, fun property holds => stopped _ ((Run.returnsResult_query_iff rfl db env property).mp holds),
    fun code holds => stopped _ ((Run.returnsError_query_iff rfl db env code).mp holds)⟩

/-- A query of one row of {name}`sample` without an order: the model permits the result
{lit}`[[1]]` and the result {lit}`[[2]]`. -/
def firstItem : Script := sql r"SELECT value FROM items LIMIT 1"

/-- The output of the query of one row is the raw choice of the two results. -/
def bothResults : Output := .oneOf [[[.integer 1]], [[.integer 2]]]

/-- B02, a choice of results, on {name}`sample` in the default environment:

* the success post that each result has one row holds, because each alternative has it;
* the success post that the result is {lit}`[[1]]` fails, because the alternative {lit}`[[2]]`
  does not have it;
* the post that the trace has the raw choice or one concrete alternative holds: the check
  visits the raw choice and each alternative, each with its own trace;
* the post that the trace has a concrete result fails, because the raw choice keeps its trace.

Proof sketch: the model decides each {name}`Sql.check` on the concrete database. -/
theorem choice_check :
    (query firstItem rfl).check (fun result _ => (match result with
      | .ok rows => rows.length == 1 | .error _ => false) = true) (ExecutionContext.initial sample {}) ∧
    ¬ (query firstItem rfl).check (fun result _ => (match result with
      | .ok rows => rows == [[.integer 1]] | .error _ => false) = true) (ExecutionContext.initial sample {}) ∧
    (query firstItem rfl).check (fun _ after => after.outputs = [bothResults] ∨
      after.outputs = [.rows [[.integer 1]]] ∨ after.outputs = [.rows [[.integer 2]]])
      (ExecutionContext.initial sample {}) ∧
    ¬ (query firstItem rfl).check (fun _ after =>
      (match after.outputs with | [.rows _] => true | _ => false) = true) (ExecutionContext.initial sample {}) := by
  decide +kernel

/-- B02, nonempty alternatives: for every property of a result, a choice of no results does not
return a result with the property, so an empty choice cannot satisfy a claim vacuously. -/
theorem empty_choice (property : List (List Value) → Prop) : ¬ (Output.oneOf []).returnsResult property := by
  simp [Output.returnsResult]

#print axioms missing_table_error
#print axioms missing_table_check
#print axioms missing_witnesses
#print axioms unmodeled_stop
#print axioms choice_check
#print axioms empty_choice

end SelectOutcomeCases
