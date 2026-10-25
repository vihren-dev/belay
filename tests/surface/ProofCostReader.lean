import Lean
import Belay.Sqlite.ProofCostPending

/-! Test reader for the S7 proof-cost collector: it prints the records of the current module
and of the imported modules, a snapshot of the declarations, and a window of heartbeats. It
imports only the collector's data module, so a control compile can import it without the
collector's handlers. -/

open Lean Elab Command Belay.Sqlite Belay.Sqlite.ProofCost

namespace ProofCostReader

/-- Print the records of the current module and then those of the imported modules, as the
checker reads them. -/
elab "#proof_cost_records" : command => do
  let env ← getEnv
  let imported := (costExtension.toEnvExtension.getState env).importedEntries
  let own := distinctRecords (costExtension.getState env)
  logInfo m!"PROOF_COSTS {(toJson (imported.foldl (· ++ ·) #[] ++ own)).compress}"

/-- Print the names, types and values of the declarations of the module, to compare a compile
with the collector and one without it. -/
elab "#proof_cost_snapshot" : command => do
  let values := (← getEnv).constants.map₂.toList.map fun (name, info) =>
    Json.mkObj [("name", toJson name.toString), ("type", toJson (reprStr info.type)),
      ("value", toJson ((info.value? true).map reprStr))]
  logInfo m!"DECLARATIONS {(toJson values).compress}"

/-- Print whether a command handler keeps Lean's incremental elaboration. -/
elab "#proof_cost_incremental " handler:ident : command => do
  let name ← liftCoreM (realizeGlobalConstNoOverload handler)
  logInfo m!"INCREMENTAL {name} {← isIncrementalElab name}"

/-- The heartbeat count at the start of a measured window. -/
initialize windowStart : IO.Ref Nat ← IO.mkRef 0

/-- Start the window of commands whose heartbeats are compared. -/
elab "#proof_cost_begin" : command => do windowStart.set (← IO.getNumHeartbeats)

/-- Print the heartbeats of this thread since {lit}`#proof_cost_begin`. -/
elab "#proof_cost_end" : command => do
  logInfo m!"WINDOW_HEARTBEATS {(← IO.getNumHeartbeats) - (← windowStart.get)}"

end ProofCostReader
