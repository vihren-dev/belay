import VerifierConformance.Classify
import Belay.Sqlite.Model.ScriptRunExamples
import Belay.Sqlite.Model.CounterReadExamples

set_option doc.verso true

/-! Examples of the comparison of a native run with the complete executions of a script
({name}`Belay.Sqlite.Model.Conformance.classifyPasses`, ADR 0017, D3, amended 2026-10-22; ADR 0019,
D4, amended 2026-10-25), checked by the kernel when the package builds. The model gives no
statement with more than one execution yet, so the script here has a first statement whose run is
built by hand with a second execution: a test input for the comparison, not a recorded SQLite
result. The native record matches the case when it matches all observations and outputs of one
complete execution. It does not match when it matches the first statement of one execution and the
second statement of another. -/

namespace Belay.Sqlite.Model.Conformance.RunPassExecutionsExamples

open Belay.Sqlite.Model Syntax Resolution.Examples ScriptRunExamples CounterReadExamples

/-- The context of the examples: the default profile, in execution mode. -/
def context : ResolveContext := { profile := defaults, mode := .execution }

/-- A second execution of the first statement, built by hand: it fails with a constraint violation
and sets {lit}`changes()` to 5. -/
def failedExecution : StatementRun.Alternative :=
  { effect := .error (.constraintViolation, {}), counts := { changes := some 5 } }

/-- The step of the pass for the statement at index 0 with {name}`failedExecution` as its second
execution; every other statement takes the model's step ({name}`runPassStep`). -/
def twoExecutionPassStep (index : Nat) (connection : Connection) (entry : Syntax.Statement × List Value) : RunPassStep :=
  if index = 0 then
    runScriptStepWith RunPassStep.ended
      (fun resolved after value run transition =>
        ranPassStep index entry.2 connection resolved after value { run with alternatives := [failedExecution] } transition)
      context none index connection entry.1 entry.2
  else runPassStep context none index connection entry.1 entry.2

/-- {lit}`PRAGMA foreign_keys = ON`, then {lit}`SELECT changes()`. -/
def script : List Syntax.Statement :=
  [.pragma (.setting .foreignKeys (some true)), .select [.expression (.call "changes" []) none "changes()"] none [] none [] [] none none]

/-- A new connection with the counters at 0. -/
def start : Connection := { state := { database := {}, counters := Counters.newConnection } }

/-- The passes of the complete executions of {name}`script`, with {name}`failedExecution`. -/
def passes : List RunPass := runPassAllWith twoExecutionPassStep 0 start (bindValues script [])

/-- The native observation of a connection with no table: the transaction is closed, and the
statement ended with the primary code. -/
def observation (code : Nat) (phase : Option ErrorPhase := none) : NativeObservation :=
  { visible := [], persisted := [], transactionOpen := false, primaryCode := code, extendedCode := code, phase }

/-- The native output of {lit}`SELECT changes()` with the value. -/
def changesOutput (value : Int) : NativeOutput :=
  { result := { columns := ["changes()"], rows := [[.integer value]], changes := none } }

/-- The native output of the pragma: no column and no row. -/
def pragmaOutput : NativeOutput := { result := { columns := [], rows := [], changes := none } }

/-- A case with a native record: the observation of the start, the observation after each
statement, and the outputs. -/
def caseOf (codes : List (Nat × Option ErrorPhase)) (outputs : List NativeOutput) : Case :=
  { version := 7, profile := defaults, schemaSql := "", migrationSql := "", schema := [], script, initial := [],
    nativeTrace := observation 0 :: codes.map fun (code, phase) => observation code phase,
    outputs := some outputs, continues := true }

/-- The script has two complete executions. -/
example : passes.length = 2 := by decide +kernel

/-- The native run that matches the first execution (the model's own) is accepted. -/
example : classifyPasses (caseOf [(0, none), (0, none)] [pragmaOutput, changesOutput 0]) start passes = .agree := by
  decide +kernel

/-- The native run that matches the second execution is accepted: the statement fails, and
{lit}`changes()` reads 5 from the connection that this execution left. -/
example : classifyPasses (caseOf [(19, some .step), (0, none)] [pragmaOutput, changesOutput 5]) start passes = .agree := by
  decide +kernel

/-- A native run that matches the first statement of the first execution and the second statement of the
second execution is rejected. -/
example : classifyPasses (caseOf [(0, none), (0, none)] [pragmaOutput, changesOutput 5]) start passes ≠ .agree := by
  decide +kernel

/-- A native run that matches the first statement of the second execution and the second statement of
the first execution is rejected. -/
example : classifyPasses (caseOf [(19, some .step), (0, none)] [pragmaOutput, changesOutput 0]) start passes ≠ .agree := by
  decide +kernel

end Belay.Sqlite.Model.Conformance.RunPassExecutionsExamples
