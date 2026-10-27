import Lean.Elab.Term
import Lean.Util.Heartbeats

set_option doc.verso true

/-! A common speculative-state and resource boundary for SQL checks. Failed attempts restore
Lean's elaboration state; exhaustion remains inconclusive and cancellation propagates. -/

namespace Belay.Sqlite.Check

open Lean Elab Term

/-- Background decoding accepts at most this many constructor and literal nodes. Larger
values can use the explicit witness API instead of the convenience checker. -/
def maxDataNodes : Nat := 8192

/-- Background decoding and generated proposals accept at most this many literal bytes. -/
def maxLiteralBytes : Nat := 65536

/-- Native replay translation receives at most this many UTF-8 bytes of proposed SQL. -/
def maxReplayBytes : Nat := 16384

/-- Background row-count draws use this finite ceiling; explicit sampling remains available
for larger databases. The bound keeps each standard random choice to one generator step. -/
def maxRandomRows : Nat := 8192

/-- At most this many supplied constants precede the ordinary random boundary values. -/
def maxRandomValues : Nat := 8192

/-- A background random proposal contains at most this many cells before validation. -/
def maxRandomCells : Nat := 8192

/-- Bound seed arithmetic by the same literal storage policy as decoded data. -/
def maxSeedBits : Nat := maxLiteralBytes * 8

/-- The default finite reduction depth permits small GROUP observations. Each checking
operation can choose another positive depth; zero disables it. -/
def defaultRecursionLimit : Nat := 4000

/-- Run one speculative attempt, restoring elaboration state if it fails or is interrupted.
A successful attempt retains its assignments and declarations, which a returned certificate
can need, but discards speculative diagnostics and editor information. Callers must fully
instantiate and certify returned proofs before accepting them. -/
def speculative (action : TermElabM α) : TermElabM α := do
  let saved ← Term.saveState
  let completed ← IO.mkRef false
  try
    let result ← action
    modifyThe Core.State fun state =>
      { state with messages := saved.meta.core.messages, infoState := saved.meta.core.infoState }
    completed.set true
    return result
  finally
    unless ← completed.get do saved.restore (restoreInfo := true)

/-- Try a candidate and discard an ordinary elaboration failure. Resource exhaustion and
interrupts propagate after restoring state; they cannot become evidence from another branch. -/
def attempt (action : TermElabM α) : TermElabM (Option α) := do
  try some <$> speculative action
  catch _ => pure none

/-- The heartbeat units left in the current budget, in the unit of {lit}`withinBudget`. When the budget is
unlimited, the units are Lean's default work limit, so a share of the budget stays finite. -/
def remainingUnits : CoreM Nat := do
  if (← getMaxHeartbeats) == 0 then return maxHeartbeats.defValue
  return (← getRemainingHeartbeats) / 1000

/-- Run a checking attempt with a fresh heartbeat origin and a finite Lean heartbeat budget.
Zero disables work, rather than using Lean's unlimited zero convention. Check again after
the action so a compiled computation cannot return an accepted result after exhausting its
budget. This is a cooperative heartbeat limit, not a hard elapsed-time limit. Runtime exhaustion
returns none; an interrupt is rethrown by {name}`tryCatchRuntimeEx`. Other errors remain
available to the caller as diagnostics, not evidence that a proposition is false. -/
def withinBudget (heartbeats : Nat) (action : TermElabM α) : TermElabM (Option α) := do
  if heartbeats == 0 then return none
  tryCatchRuntimeEx
    (some <$> speculative (withCurrHeartbeats <|
      withTheReader Core.Context (fun context => { context with maxHeartbeats := heartbeats * 1000 }) <|
        withOptions (maxHeartbeats.set · heartbeats) do
          let result ← action
          checkSystem "SQL checking budget"
          return result))
    (fun error => if error.isRuntime then pure none else throw error)

end Belay.Sqlite.Check
