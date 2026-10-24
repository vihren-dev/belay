import Belay.Sqlite.CheckProof
import Belay.Sqlite.CounterexampleShrink

set_option doc.verso true

/-! The shared proof/counterexample operation. Generators supply candidates, and tactics
supply proof terms; both cross the original-proposition certificate boundary. Replay is a
separate acceptance condition for the user-facing SQL report. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term

/-- The outcome of a checking attempt. Functions returning this type must certify the
original proposition; constructing a value of this type alone supplies no evidence. -/
inductive Result where
  /-- A certified proof of the original proposition and its checked tactic script. -/
  | proved (proof : Proven)
  /-- A concrete witness and certified proof of the original proposition's negation.
  A SQL diagnostic additionally needs a replay of the original claim at this witness. -/
  | refuted (witness : Witness) (proof : Expr)
  /-- No certificate was found. This says nothing about the proposition's truth. -/
  | unknown

/-- Try caller-selected automation, then a finite sequence of concrete candidates, in order.
The automation result is recertified against the original proposition, and its proposed tactic
is independently elaborated and certified against that proposition. Each candidate checks
all supplied inputs and implication premises before it can refute that same proposition.
Failures restore speculative elaboration state; exhaustion and cancellation propagate to the
outer budget. Use this primitive for explicit schemas or arbitrary Lean predicates. -/
def checkCandidates (proposition : Expr) (candidates : TermElabM (Array Witness))
    (prove : Expr → TermElabM (Option Proven) := fun proposition => tryProof proposition)
    (excluded : Array Name := #[]) (excludedLocals : Array FVarId := #[]) : TermElabM Result := do
  let proven ← attempt do
    let some result ← prove proposition | throwError "proof automation found no certificate"
    discard <| certify proposition result.proof excluded excludedLocals
    proveWith proposition result.tactic excluded excludedLocals
  if let some proof := proven then return .proved proof
  for witness in ← candidates do
    checkSystem "SQL candidate search"
    if let some proof ← attempt (refuteWitness proposition witness excluded excludedLocals) then
      return .refuted witness proof
  return .unknown

end Belay.Sqlite.Check
