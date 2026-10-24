import ProofCostRecords

/-! Test-only hook: preserve normal declaration elaboration while retaining native
body traces for completed async snapshots and serialized records. -/
open Lean Elab Command
namespace ProofCostExperiment

/-- Keep the body class while suppressing unrelated profiler output. -/
def nativeOptions (opts : Options) : Options :=
  let opts := opts.setBool `trace.profiler true
  let opts := opts.setBool `trace.profiler.useHeartbeats true
  let opts := opts.setBool `trace.Elab.definition.value true
  trace.profiler.threshold.set opts maximumExactHeartbeat

/-- Delegate normal declaration elaboration while enabling the native body trace. -/
@[command_elab Lean.Parser.Command.declaration]
def elaborateMeasured : CommandElab := fun stx => do
  let before ← get
  let start ← IO.getNumHeartbeats
  let enabled := proofCost.enabled.get (← getOptions)
  withScope (fun scope => { scope with opts := if enabled then nativeOptions scope.opts
      else scope.opts }) do
    elabDeclaration stx
  let stop ← IO.getNumHeartbeats
  let after ← get
  let moduleName := (← getEnv).mainModule.toString
  let immediate := after.traceState.traces.toArray.extract before.traceState.traces.size
    after.traceState.traces.size |>.foldl (fun found trace => found ++ collect moduleName trace.msg) #[]
  let pending : Pending := {
    moduleName := moduleName
    offset := (stx.getPos?.getD 0).byteIdx
    asynchronous := Elab.async.get (← getOptions)
    commandHeartbeats := stop - start
    immediate := immediate
    tasks := after.snapshotTasks.extract before.snapshotTasks.size after.snapshotTasks.size }
  modifyEnv fun env => costs.addEntry env pending


end ProofCostExperiment
