import Belay.Sqlite.CheckBudget
import Belay.Sqlite.CheckCandidates
import Belay.Sqlite.CheckSamples
import Belay.Sqlite.CheckReplay

set_option doc.verso true

/-! One bounded operation for commands, tactics and automatic checks. Kernel certification
controls either truth result; replay is an additional condition for reporting an SQL witness. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term

/-- A checked outcome together with replay evidence. Only the checking operation below establishes the
certificate/replay contract; directly constructing this display record proves nothing. -/
structure Outcome where
  /-- Proved or refuted only after exact-proposition certification; unknown gives no evidence. -/
  result : Result := .unknown
  /-- Reconstructions and original-query observations for a reported refutation. -/
  replays : Array Replay.Report := #[]

/-- Try proof automation, then the shared candidate generator, and require replay before
reporting a counterexample. An unreplayable candidate is skipped so later candidates can
still supply a report within the same budget. Optional shrinking retains only recertified
witnesses with valid replays; absent, rejected or unchanged shrinks retain the original
certificate and replay. The budget
covers the complete operation. A separately configurable recursion limit uses {name}`defaultRecursionLimit`,
which permits small GROUP observations under cooperative reduction. Both limits are finite;
zero disables checking. The caller's recursion option is restored afterwards. Exhaustion
returns unknown and cancellation
propagates after state cleanup. Explicit candidates and custom automation remain available. -/
def check (proposition : Expr) (heartbeats : Nat) (samples : SampleConfig := {})
    (shrinkAttempts : Nat := 16)
    (prove : Expr → TermElabM (Option Proven) := fun proposition => tryProof proposition)
    (excluded : Array Name := #[]) (excludedLocals : Array FVarId := #[])
    (recursionLimit : Nat := defaultRecursionLimit) : TermElabM Outcome := do
  if recursionLimit == 0 then return {}
  let outcome : Option (Option Outcome) ← withOptions (maxRecDepth.set · recursionLimit) <|
    withinBudget heartbeats <| attempt do
      let result ← checkCandidates proposition (pure #[]) prove excluded excludedLocals
      if let .proved _ := result then return { result }
      let accepted : Option Outcome ← visitCandidates proposition samples fun witness => do
        let proof ← refuteWitness proposition witness excluded excludedLocals
        let reports ← replayClaim proposition witness excluded excludedLocals
        let result := Result.refuted witness proof
        if shrinkAttempts == 0 then return { result, replays := reports }
        let smaller : Option Outcome ← attempt do
          let proposals ← shrinkProposals witness excluded excludedLocals
          if proposals.isEmpty then return { result, replays := reports }
          -- The convenience checker tries one shared shrink round. The public
          -- shrinkCertified primitive permits repeated or custom rounds.
          let (smaller, proof) ← shrinkCertified proposition witness (fun current =>
            pure (if current.database == witness.database then proposals else []))
            shrinkAttempts excluded excludedLocals
          if smaller.database == witness.database then return { result, replays := reports }
          let reports ← replayClaim proposition smaller excluded excludedLocals
          return { result := .refuted smaller proof, replays := reports }
        return smaller.getD { result := .refuted witness proof, replays := reports }
      return accepted.getD {}
  return (outcome.bind id).getD {}

end Belay.Sqlite.Check
