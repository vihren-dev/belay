import Lean

/-! Test-only records, readers and a common benchmark timer for the S7 experiment.
Importing this module alone keeps the ordinary declaration elaborator. -/

open Lean Elab Command

namespace ProofCostExperiment

register_option proofCost.enabled : Bool := {
  defValue := true
  descr := "enable the test-only native body profiler" }

/-- One native body-elaboration measurement, in internal heartbeat units. -/
structure Cost where
  /-- Module identity, independent of its filesystem location. -/
  moduleName : String
  /-- Native declaration label; anonymous/private stability is tested separately. -/
  declaration : String
  /-- An unavailable or failed measurement never becomes a completed zero. -/
  status : String
  /-- Exact internal units when both native Float endpoints are exactly representable. -/
  heartbeats : Option Nat
  /-- One user-facing budget unit is exactly 1000 internal heartbeat units. -/
  unit : String := "internal-heartbeat"
  /-- Measurements from different compilers must not be compared as regressions. -/
  compiler : String := Lean.versionString
  /-- This boundary excludes headers and later kernel checking; export adds the async mode. -/
  scheme : String := "native-definition-value-v1"
  deriving Inhabited, ToJson

/-- Extract the eager native name label without evaluating arbitrary lazy messages. -/
partial def label : MessageData → Option String
  | .ofFormatWithInfos value => some value.fmt.pretty
  | .withContext _ inner | .withNamingContext _ inner | .nest _ inner | .group inner
  | .tagged _ inner | .ofOriginatingSyntax _ inner => label inner
  | .ofWidget _ _ | .ofGoal _ | .compose _ _ | .trace _ _ _ | .ofLazy _ _ => none

/-- Largest counter endpoint below the point where adjacent integers can share a Float. -/
def maximumExactHeartbeat : Nat := 9007199254740991

/-- Retain exact internal units only inside Float's exact integer range. -/
def count (data : TraceData) : Option Nat :=
  if data.startTime >= 0 && data.stopTime >= data.startTime && data.stopTime <= maximumExactHeartbeat.toFloat &&
      data.startTime.toUInt64.toNat.toFloat == data.startTime &&
      data.stopTime.toUInt64.toNat.toFloat == data.stopTime then
    some (data.stopTime.toUInt64.toNat - data.startTime.toUInt64.toNat)
  else none

/-- Find native body nodes through structured trace/message wrappers, including children. -/
partial def collect (moduleName : String) : MessageData → Array Cost
  | .trace data message children => Id.run do
    let nested := children.foldl (fun found child => found ++ collect moduleName child) #[]
    if data.cls != `Elab.definition.value then return nested
    let some declaration := label message | return nested
    let heartbeats := count data
    let status := if data.result? != some .success then "failed"
      else if heartbeats.isNone then "precision-unavailable" else "completed"
    return nested.push { moduleName, declaration, status, heartbeats }
  | .withContext _ inner | .withNamingContext _ inner | .nest _ inner | .group inner
  | .tagged _ inner | .ofOriginatingSyntax _ inner => collect moduleName inner
  | .ofWidget _ inner => collect moduleName inner
  | .compose first second => collect moduleName first ++ collect moduleName second
  | .ofFormatWithInfos _ | .ofGoal _ | .ofLazy _ _ => #[]

/-- A command retains tasks without waiting for its asynchronous proof. -/
structure Pending where
  /-- The source module that scheduled this declaration. -/
  moduleName : String
  /-- A path-independent byte offset distinguishes anonymous declaration commands. -/
  offset : Nat
  /-- Native async and synchronous measurements use distinct measurement schemes. -/
  asynchronous : Bool
  /-- The command timer includes synchronous work only; it is used for overhead probes. -/
  commandHeartbeats : Nat
  /-- Synchronous body traces already available when the command returns. -/
  immediate : Array Cost
  /-- Proof snapshots may still be running at the return of the declaration command. -/
  tasks : Array (Language.SnapshotTask Language.SnapshotTree)
  deriving Inhabited

/-- Harvest completed snapshots at export, including traces moved into diagnostics. -/
def Pending.finish (pending : Pending) : Array Cost := Id.run do
  let mut found := pending.immediate
  for task in pending.tasks do
    for snapshot in task.get.getAll do
      for trace in snapshot.traces.traces.toArray do
        found := found ++ collect pending.moduleName trace.msg
      for message in snapshot.diagnostics.msgLog.toList do
        found := found ++ collect pending.moduleName message.data
  return found.map fun cost =>
    let declaration := if cost.declaration.endsWith "._example" || cost.declaration == "_example"
      then s!"{cost.declaration}@{pending.offset}" else cost.declaration
    let mode := if pending.asynchronous then "async" else "sync"
    { cost with declaration, scheme := s!"{cost.scheme}-{mode}" }

/-- Only plain records are serialized; pending snapshot tasks stay in the current process. -/
initialize costs : PersistentEnvExtension Cost Pending (Array Pending) ←
  registerPersistentEnvExtension {
    name := `ProofCostExperiment.costs
    mkInitial := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn := fun entries entry => entries.push entry
    exportEntriesFn := fun entries => entries.foldl (fun found entry => found ++ entry.finish) #[] }

/-- A command timer is not a completed async body timer. Export only body records. -/
elab "#proof_cost_commands" : command => do
  let entries := costs.getState (← getEnv)
  let values := entries.map fun entry => Json.mkObj [
    ("offset", toJson entry.offset), ("heartbeats", toJson entry.commandHeartbeats),
    ("declarations", toJson (entry.finish.map (·.declaration))),
    ("snapshots", toJson (entry.tasks.toList.flatMap fun task => task.get.getAll.toList.map (·.desc)))]
  logInfo m!"COMMAND_COSTS {(toJson values).compress}"

/-- Test reader: imported data is read from the olean without re-elaborating its proofs. -/
elab "#proof_cost_records" : command => do
  let env ← getEnv
  let imported := (costs.toEnvExtension.getState env).importedEntries
  let records := imported.foldl (· ++ ·) #[] ++
    (costs.getState env).foldl (fun found entry => found ++ entry.finish) #[]
  logInfo m!"PROOF_COSTS {(toJson records).compress}"

/-- Compare exact checked declaration expressions between instrumented and control compiles. -/
elab "#proof_cost_snapshot" : command => do
  let declarations := (← getEnv).constants.map₂.toList
  let values := declarations.map fun (name, info) =>
    Json.mkObj [("name", toJson name.toString), ("type", toJson (reprStr info.type)),
      ("value", toJson ((info.value? true).map reprStr))]
  logInfo m!"DECLARATIONS {(toJson values).compress}"

/-- The benchmark window excludes imports and later serialization in both compiles. -/
initialize benchmarkStart : IO.Ref Nat ← IO.mkRef 0

/-- Start the common synchronous command window before the surface proof sample. -/
elab "#proof_cost_begin" : command => do benchmarkStart.set (← IO.getNumHeartbeats)

/-- Report this thread's synchronous command window, including collector work when enabled. -/
elab "#proof_cost_end" : command => do
  let stop ← IO.getNumHeartbeats
  let start ← benchmarkStart.get
  logInfo m!"WINDOW_HEARTBEATS {stop - start}"

end ProofCostExperiment
