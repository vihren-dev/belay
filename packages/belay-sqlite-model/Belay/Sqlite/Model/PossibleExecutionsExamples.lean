import Belay.Sqlite.Model.ScriptRunSingleton
import Belay.Sqlite.Model.CounterReadExamples
import Belay.Sqlite.Model.ForeignKeyExamples

set_option doc.verso true

/-! Examples of the possible executions of a statement (ADR 0019, D4, amended 2026-10-25).

* Every current statement kind has one execution: a query, a write without and with foreign keys,
  a DDL statement, a pragma, a transaction control statement and a statement that SQLite refuses
  to prepare. The complete executions of each script are then the one run of
  {lit}`Belay.Sqlite.Model.runScriptFrom`.
* A statement with a permitted result list ({lit}`Belay.Sqlite.Model.Output.oneOf`) stands for
  executions that share the next connection ({lit}`Belay.Sqlite.Model.StatementExecution.expand`).
* A statement run that is built by hand with a second execution makes a script with two complete
  executions. A later statement runs from the connection of the execution that reached it. The
  second execution is a test input, not a recorded SQLite result: the model gives no statement
  with more than one execution yet. -/

namespace Belay.Sqlite.Model.PossibleExecutionsExamples

open Belay.Sqlite.Model Syntax Resolution.Examples ScriptRunExamples CounterExamples CounterReadExamples ForeignKeyExamples

/-- The context of the examples: the default profile, in execution mode. -/
def context : ResolveContext := { profile := defaults, mode := .execution }

/-- The outputs of all complete executions of the statements, from the empty database on a new
connection, with foreign keys on or off. -/
def allOutputs (script : List Syntax.Statement) (foreignKeys : Bool := false) : List (List Output) :=
  (runScriptAllFrom context none 0 { state := { database := {}, counters := Counters.newConnection }, foreignKeys }
    (bindValues script [])).map (·.outputs)

/-- The outputs of the model's own traversal of the statements, on the same connection as
{lit}`allOutputs`. -/
def ownOutputs (script : List Syntax.Statement) (foreignKeys : Bool := false) : List Output :=
  (runScriptFrom context none 0 { state := { database := {}, counters := Counters.newConnection }, foreignKeys }
    (bindValues script [])).outputs

/-- The singleton law for a script: its one complete execution is the traversal of the model. -/
def singleton (script : List Syntax.Statement) (foreignKeys : Bool := false) : Bool :=
  allOutputs script foreignKeys == [ownOutputs script foreignKeys]

/-- A query (and a query that SQLite refuses to prepare, on the table that is not there), a write
without foreign keys that succeeds and one that fails, and DDL. -/
example : singleton [selectNames, createT, insertT "1" "a", insertT "1" "b", selectNames,
    .dropTable (name! "t") false] = true := by decide +kernel

/-- Transaction control, a pragma, and a write that sets a foreign key. -/
example : singleton [.begin, createT, .pragma (.setting .foreignKeys (some true)), insertT "1" "a",
    .rollback, selectNames, .commit] = true := by decide +kernel

/-- A write with foreign keys on: a cascade, a failed parent delete and an update of a parent. -/
example : singleton (schema .cascade .noAction ++ [deleteOne, updateOne, child (.numeric "9")]) true = true := by
  decide +kernel
example : singleton (schema .noAction .noAction ++ [deleteOne, updateOne, child .null]) true = true := by
  decide +kernel

/-- A query with a permitted result list is one execution, with the output {lit}`Output.oneOf`. -/
example : allOutputs [createT, insertT "1" "b", insertT "2" "a", firstOf (.identifier (name! "name") .none)] =
    [[.done 0, .done 1, .done 1, .oneOf [[[textValue "a"]], [[textValue "b"]]]]] := by decide +kernel

/-- For a script of the statements of the examples, the one complete execution is the traversal. -/
theorem allOutputs_eq_own (script : List Syntax.Statement) (foreignKeys : Bool) :
    allOutputs script foreignKeys = [ownOutputs script foreignKeys] := by
  simp [allOutputs, ownOutputs, runScriptAllFrom_eq]

/-- A step of every statement has at most one execution: the number of executions of
{lit}`runScriptStep` is 0 when the run ends and 1 otherwise. -/
theorem executions_length_le_one (index : Nat) (connection : Connection) (statement : Syntax.Statement)
    (parameters : List Value) : (runScriptStep context none index connection statement parameters).executions.length ≤ 1 := by
  cases step : runScriptStep context none index connection statement parameters with
  | ended reason => simp [RunStep.executions]
  | continued output next others => simp [RunStep.executions, runScriptStep_others step]

/-- The connection after the table and the two rows of the query with a permitted result list. -/
def afterRows : Connection :=
  (runScriptFrom context none 0 { state := { database := {}, counters := Counters.newConnection } }
    (bindValues [createT, insertT "1" "b", insertT "2" "a"] [])).connection

/-- The one execution of the query with a permitted result list stands for two executions with the
two rows as their outputs: the correspondence of {lit}`Output.oneOf` with executions. -/
example : ((runScriptStep context none 3 afterRows (firstOf (.identifier (name! "name") .none)) []).executions.flatMap
      StatementExecution.expand).map (·.output) = [.rows [[textValue "a"]], .rows [[textValue "b"]]] := by
  decide +kernel

/-- A second execution for {lit}`createT`, built by hand for the test: it leaves the empty database
and sets {lit}`changes()` to 5. The model's own execution of {lit}`createT` creates the table and
leaves {lit}`changes()` as it is. -/
def secondCreate : StatementRun.Alternative := { effect := .ok {}, counts := { changes := some 5 } }

/-- The step of the script with two executions for the statement at index 0: the model's step with
{lit}`secondCreate` added as a second execution of its run. Every other statement takes the model's
step. -/
def twoExecutionStep (index : Nat) (connection : Connection) (entry : Syntax.Statement × List Value) : RunStep :=
  if index = 0 then
    runScriptStepWith RunStep.ended
      (fun resolved after value run transition =>
        ranScriptStep index entry.2 connection resolved after value { run with alternatives := [secondCreate] } transition)
      context none index connection entry.1 entry.2
  else runScriptStep context none index connection entry.1 entry.2

/-- The script of the test: the CREATE with two executions, a read of {lit}`changes()`, and a read of the
table. -/
def twoExecutionScript : List (Syntax.Statement × List Value) :=
  bindValues [createT, readOf "changes", selectNames] []

/-- A new connection with the counters at 0, the start of the test. -/
def newConnection : Connection := { state := { database := {}, counters := Counters.newConnection } }

/-- The step at index 0 has two executions: the model's own first, and the built one. -/
example : ((twoExecutionStep 0 newConnection (createT, [])).executions.map (·.output)) = [.done 0, .done 0] := by
  decide +kernel

/-- The script has two complete executions, each one sequence: after its own CREATE, each later
statement reads the counter and the table of the connection that execution left. In the first
execution {lit}`changes()` is 0 and the table is there with no row; in the second it is 5 and the
table is not there (error 1). -/
example : (runScriptAllWith twoExecutionStep 0 newConnection twoExecutionScript).map (·.outputs) =
    [[.done 0, .rows [[.integer 0]], .rows []], [.done 0, .rows [[.integer 5]], .error 1]] := by
  decide +kernel

end Belay.Sqlite.Model.PossibleExecutionsExamples
