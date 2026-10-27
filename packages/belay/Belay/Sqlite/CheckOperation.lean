import Belay.Sqlite.CheckBudget
import Belay.Sqlite.CheckCandidates
import Belay.Sqlite.CheckAutoProof
import Belay.Sqlite.CheckSamples
import Belay.Sqlite.CheckReplay
import Belay.Sqlite.CheckObservation

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
  /-- The branch and the failing observation of a reported refutation of a claim about programs, from the model's
  run at the witness. None when the claim is no such claim or the text is out of budget. -/
  observation : Option String := none

/-- Try proof automation, then the shared candidate generator, and require replay before
reporting a counterexample. An unreplayable candidate is skipped so later candidates can
still supply a report within the same budget. Optional shrinking retains only recertified
witnesses with valid replays; absent, rejected or unchanged shrinks retain the original
certificate and replay. The budget
covers the complete operation; the shrinking of a witness uses at most {name}`shrinkShare` of what is left, so a
witness that is certified and replayed is reported even when shrinking uses its share. A separately configurable recursion limit uses {name}`defaultRecursionLimit`,
which permits small GROUP observations under cooperative reduction. Both limits are finite;
zero disables checking. The caller's recursion option is restored afterwards. Exhaustion
returns unknown and cancellation
propagates after state cleanup. Explicit candidates and custom automation remain available. -/
def check (proposition : Expr) (heartbeats : Nat) (samples : SampleConfig := {})
    (shrinkAttempts : Nat := 16)
    (prove : Expr → TermElabM (Option Proven) := defaultProof)
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
        let observation ← observeFailure proposition witness excluded excludedLocals
        let original : Outcome := { result := .refuted witness proof, replays := reports, observation }
        if shrinkAttempts == 0 then return original
        -- Shrinking may use its share of the budget that is left. A certified, replayed witness is kept when
        -- shrinking uses its share without a smaller witness.
        let smaller : Option (Option Outcome) ← withinBudget (shrinkShare.units (← remainingUnits)) <| attempt do
          let proposals ← shrinkProposals witness excluded excludedLocals
          if proposals.isEmpty then return original
          -- The convenience checker tries one shared shrink round. The public
          -- shrinkCertified primitive permits repeated or custom rounds.
          let (smaller, proof) ← shrinkCertified proposition witness (fun current =>
            pure (if current.database == witness.database then proposals else []))
            shrinkAttempts excluded excludedLocals
          if smaller.database == witness.database then return original
          let reports ← replayClaim proposition smaller excluded excludedLocals
          let observation ← observeFailure proposition smaller excluded excludedLocals
          return { result := .refuted smaller proof, replays := reports, observation }
        return (smaller.bind id).getD original
      return accepted.getD {}
  return (outcome.bind id).getD {}

end Belay.Sqlite.Check
