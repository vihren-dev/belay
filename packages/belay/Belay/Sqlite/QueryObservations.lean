import Belay.Sqlite.Queries
import Belay.Sqlite.RunResultSteps

set_option doc.verso true

/-! The run observations of a query and its output: for a query script ({lit}`Script.isQuery`), the
run in the default environment returns a result or an error exactly when the output of the query
({lit}`Script.outputOn`) does. {lit}`Holds`, {lit}`Empty` and {lit}`Fails` are such observations, so
a law about the output of a query gives a law about them. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every query script, its statements are exactly one statement with its bound values. Proof
sketch: the empty and multiple-statement cases fail {name}`Script.isQuery`. -/
theorem Script.singleton_of_isQuery {script : Script} (query : script.isQuery = true) :
    ∃ statement values, script.statements = [(statement, values)] := by
  cases found : script.statements with
  | nil => simp [Script.isQuery, found] at query
  | cons head tail =>
    cases tail with
    | nil => exact ⟨head.1, head.2, rfl⟩
    | cons next tail => simp [Script.isQuery, found] at query

/-- For every query script and database, the script is one statement with its values, and the output
of the script on the database ({name}`Script.outputOn`) is the output of the step of that statement on
the connection of the database, with no clock, at index 0. Proof sketch: the run of a script of one
statement gives the output of its one step, also when the step ends the run. -/
theorem Script.outputOn_isQuery {script : Script} (query : script.isQuery = true) (db : Database) :
    ∃ statement values, script.statements = [(statement, values)] ∧
      script.outputOn db = some (runScriptStep runContext none 0 db.raw.connection statement values).output := by
  obtain ⟨statement, values, one⟩ := Script.singleton_of_isQuery query
  refine ⟨statement, values, one, ?_⟩
  unfold Script.outputOn Database.Raw.run Script.runOn
  rw [one]
  cases step : runScriptStep runContext none 0 db.raw.connection statement values <;>
    simp [runScriptFrom, step, RunStep.output]

/-- For every query script, database and property {lit}`Q` of a result: the run of the script in the
default environment returns a result with {lit}`Q` ({name}`Run.returnsResult`) exactly when the script
has an output on the database ({name}`Script.outputOn`) that returns a result with {lit}`Q`. Proof
sketch: {name}`Run.send_returnsResult_iff` reads the step of the one statement, and
{name}`Script.outputOn_isQuery` gives the same step. -/
theorem Script.returnsResult_iff_outputOn {script : Script} (query : script.isQuery = true) (db : Database)
    (property : List (List Value) → Prop) :
    (db.run script).returnsResult property ↔
      ∃ output, script.outputOn db = some output ∧ output.returnsResult property := by
  obtain ⟨statement, values, one, found⟩ := Script.outputOn_isQuery query db
  have length : script.statements.length = 1 := by simp [one]
  rw [Run.send_returnsResult_iff length db Env.default property, found]
  simp only [Option.some.injEq, exists_eq_left']
  have same : script.statements[0]'(by rw [length]; exact Nat.one_pos) = (statement, values) := by simp [one]
  rw [same]
  rfl

/-- For every query script, database and property {lit}`E` of a result code: the run of the script in
the default environment returns an error with {lit}`E` ({name}`Run.returnsError`) exactly when the
script has an output on the database that is such an error. Proof sketch: as
{name}`Script.returnsResult_iff_outputOn`, with {name}`Run.send_returnsError_iff`. -/
theorem Script.returnsError_iff_outputOn {script : Script} (query : script.isQuery = true) (db : Database)
    (property : Nat → Prop) :
    (db.run script).returnsError property ↔
      ∃ output, script.outputOn db = some output ∧ output.returnsError property := by
  obtain ⟨statement, values, one, found⟩ := Script.outputOn_isQuery query db
  have length : script.statements.length = 1 := by simp [one]
  rw [Run.send_returnsError_iff length db Env.default property, found]
  simp only [Option.some.injEq, exists_eq_left']
  have same : script.statements[0]'(by rw [length]; exact Nat.one_pos) = (statement, values) := by simp [one]
  rw [same]
  rfl

/-- For every query script, database, output and property {lit}`Q` of a result: if the output of the
script on the database is the output, then the run of the script in the default environment returns
a result with {lit}`Q` exactly when the output does. Proof sketch:
{name}`Script.returnsResult_iff_outputOn`. -/
theorem Script.returnsResult_of_outputOn {script : Script} (query : script.isQuery = true) {db : Database}
    {output : Output} (found : script.outputOn db = some output) (property : List (List Value) → Prop) :
    (db.run script).returnsResult property ↔ output.returnsResult property := by
  simp [Script.returnsResult_iff_outputOn query, found]

/-- For every query script, database, output and property {lit}`E` of a result code: if the output of
the script on the database is the output, then the run of the script in the default environment
returns an error with {lit}`E` exactly when the output is such an error. Proof sketch:
{name}`Script.returnsError_iff_outputOn`. -/
theorem Script.returnsError_of_outputOn {script : Script} (query : script.isQuery = true) {db : Database}
    {output : Output} (found : script.outputOn db = some output) (property : Nat → Prop) :
    (db.run script).returnsError property ↔ output.returnsError property := by
  simp [Script.returnsError_iff_outputOn query, found]

/-- For every query script, database and output of the script on the database: {name}`Holds` of the
script holds exactly when the output has a row in each result ({name}`Output.hasRows`). Proof sketch:
{name}`Script.returnsResult_of_outputOn` and {name}`Output.hasRows_iff_returnsResult`. -/
theorem Holds.iff_of_outputOn {script : Script} {db : Database} {output : Output}
    (found : script.outputOn db = some output) (query : script.isQuery = true := by check_query) :
    Holds script db query ↔ output.hasRows = true := by
  rw [Holds, Script.returnsResult_of_outputOn query found, Output.hasRows_iff_returnsResult]

/-- For every query script, database and output of the script on the database: {name}`Empty` of the
script holds exactly when no result of the output has a row ({name}`Output.hasNoRows`). Proof sketch:
{name}`Script.returnsResult_of_outputOn` and {name}`Output.hasNoRows_iff_returnsResult`. -/
theorem Empty.iff_of_outputOn {script : Script} {db : Database} {output : Output}
    (found : script.outputOn db = some output) (query : script.isQuery = true := by check_query) :
    Empty script db query ↔ output.hasNoRows = true := by
  rw [Empty, Script.returnsResult_of_outputOn query found, Output.hasNoRows_iff_returnsResult]

/-- For every query script, database and output of the script on the database: {name}`Fails` of the
script holds exactly when the output is an error ({name}`Output.isError`). Proof sketch:
{name}`Script.returnsError_of_outputOn` and {name}`Output.isError_iff_returnsError`. -/
theorem Fails.iff_of_outputOn {script : Script} {db : Database} {output : Output}
    (found : script.outputOn db = some output) (query : script.isQuery = true := by check_query) :
    Fails script db query ↔ output.isError = true := by
  rw [Fails, Script.returnsError_of_outputOn query found, Output.isError_iff_returnsError]

end Belay.Sqlite
