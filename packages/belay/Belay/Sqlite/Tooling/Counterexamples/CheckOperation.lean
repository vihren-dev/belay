import Belay.Sqlite.Tooling.Counterexamples.CheckCandidates
import Belay.Sqlite.Tooling.Counterexamples.CheckAutoProof
import Belay.Sqlite.Tooling.Counterexamples.CheckSamples
import Belay.Sqlite.Tooling.Counterexamples.CheckReplay
import Belay.Sqlite.Tooling.Counterexamples.CheckObservation
import Belay.Sqlite.Tooling.Counterexamples.CheckWitnessText

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
  /-- The database and environment of a reported refutation as a user reads them. None when there is
  no refutation, or when the budget did not allow the text ({name}`describeWitness`). -/
  witness : Option WitnessText := none
  /-- Why the result is unknown, when a limit of the search explains it, for example the time limit
  of compiled work ({name}`timeLimitReason`), or a refuted candidate that has no SQLite replay. -/
  reason : Option String := none

/-- Try proof automation, then the shared candidate generator, and require replay before
reporting a counterexample. An unreplayable candidate is skipped so later candidates can
still supply a report within the same budget. Optional shrinking retains only recertified
witnesses with valid replays; absent, rejected or unchanged shrinks retain the original
certificate and replay. With a screen, shrinking takes at most {lit}`shrinkAttempts` screened
steps ({name}`screenedShrinkProposal`) and certifies only their result, so it adds at most one
certification after a replayable witness; without one, the kernel certifies at most
{lit}`shrinkAttempts` proposals ({name}`shrinkCertified`). The budget
covers the complete operation; the shrinking of a witness uses at most {name}`shrinkShare` of what is left, so a
witness that is certified and replayed is reported even when shrinking uses its share. A separately configurable recursion limit uses {name}`defaultRecursionLimit`,
which permits small GROUP observations in the kernel and the elaborator. Both limits are finite;
zero disables checking. The caller's recursion option is restored afterwards. Exhaustion
returns unknown and cancellation
propagates after state cleanup. Explicit candidates and custom automation remain available.
The certificate audit of the operation walks each accepted constant once ({name}`withAuditCache`).
Compiled work of the operation ends at {name}`SampleConfig.timeLimit` ({name}`withCompiledLimit`); an
unknown result that the limit, a claim without a screen or a refutation without a replay explains has its reason
({name}`recordedReason`). -/
def check (proposition : Expr) (heartbeats : Nat) (samples : SampleConfig := {})
    (shrinkAttempts : Nat := 16)
    (prove : Expr → TermElabM (Option Proven) := defaultProof)
    (excluded : Array Name := #[]) (excludedLocals : Array FVarId := #[])
    (recursionLimit : Nat := defaultRecursionLimit) : TermElabM Outcome := do
  if recursionLimit == 0 then return {}
  withCompiledLimit samples.timeLimit do
  let outcome : Option (Option Outcome) ← withOptions (maxRecDepth.set · recursionLimit) <|
    withAuditCache excluded <| withinBudget heartbeats <| attempt do
      let result ← checkCandidates proposition (pure #[]) prove excluded excludedLocals
      if let .proved _ := result then return { result }
      let accepted : Option Outcome ← visitCandidates proposition samples fun witness screened => do
        let proof ← refuteWitness proposition witness excluded excludedLocals
        let reports ← try replayClaim proposition witness excluded excludedLocals
          catch error =>
            recordReason s!"the kernel refutes the claim on a database, but the checker could not build its SQLite \
              replay ({← error.toMessageData.toString}), so it reports no counterexample. State the claim about \
              a query, a script or a run of a query to get a replay, or prove the negation on a database with \
              `sql_refute (db := database)`"
            throw error
        let observation ← observeFailure proposition witness excluded excludedLocals
        let text ← describeWitness witness excluded excludedLocals
        let original : Outcome :=
          { result := .refuted witness proof, replays := reports, observation, witness := text }
        if shrinkAttempts == 0 then return original
        -- Shrinking may use its share of the budget that is left. A certified, replayed witness is kept when
        -- shrinking uses its share without a smaller witness.
        let smaller : Option (Option Outcome) ← withinBudget (shrinkShare.units (← remainingUnits)) <| attempt do
          let (smaller, proof) ← match screened with
            | some (screen, value) =>
              -- The screen chooses the smaller database; the kernel certifies only that one.
              let some smaller ← screenedShrinkProposal witness screen value shrinkAttempts excluded excludedLocals
                | return original
              pure (smaller, ← refuteWitness proposition smaller excluded excludedLocals)
            | none =>
              -- Without a screen, the kernel certifies each proposal of one shared shrink round. The
              -- public shrinkCertified primitive permits repeated or custom rounds.
              let proposals ← shrinkProposals witness excluded excludedLocals
              if proposals.isEmpty then return original
              shrinkCertified proposition witness (fun current =>
                pure (if current.database == witness.database then proposals else []))
                shrinkAttempts excluded excludedLocals
          if smaller.database == witness.database then return original
          let reports ← replayClaim proposition smaller excluded excludedLocals
          let observation ← observeFailure proposition smaller excluded excludedLocals
          let text ← describeWitness smaller excluded excludedLocals
          return { result := .refuted smaller proof, replays := reports, observation, witness := text }
        return (smaller.bind id).getD original
      return accepted.getD {}
  let outcome := (outcome.bind id).getD {}
  if outcome.result matches .unknown then return { outcome with reason := ← recordedReason }
  return outcome

end Belay.Sqlite.Check
