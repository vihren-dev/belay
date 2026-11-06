import Belay

open Lean Elab Term Meta Belay.Sqlite

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_search_test.py`: the search screens the candidates
while it generates them ({lit}`Sampling.candidates` with a stop test), and each value of the value
pool gets a share of the candidate count ({lit}`Check.valueShare`). -/

namespace CandidateSharesFixture

/-- Checks the stop test of {name}`Sampling.candidates` and the share of each value in
{name}`Check.visitCandidates` ({name}`Check.valueShare`): the list ends after the first
candidate that passes the stop test; after a rejected certificate the search continues with a
later candidate; and with 200 candidates, the value NULL, which the screen never accepts, leaves
enough of the count for the value 1. Before the share, NULL used all 200. -/
def valueShares : TermElabM Unit := do
  let base := Sampling.defaultSchema
  let all := Sampling.candidates base [] none 2 3 0 2 100000
  let stopped := Sampling.candidates base [] none 2 3 0 2 100000 fun index _ => index == 5
  unless stopped.toList.map (·.raw) == (all.toList.take 6).map (·.raw) do
    throwError "the candidates do not end after the first one that passes the stop test"
  unless Check.valueShare 3 16 false == 0 && Check.valueShare 200 16 false == 12 do
    throwError "the value share is not an equal share of what is left"
  let proposition ← elabTerm (← `(∀ v : Value, v = v)) none
  let hasRows (database : Database) := database.raw.rows.any (!·.isEmpty)
  let rejected ← IO.mkRef (none : Option Database)
  let accepted ← Check.visitCandidates proposition
      { candidates := 200, screen := some fun database value => value == .integer 1 && hasRows database }
    fun witness screened => do
      let some (_, value) := screened | throwError "no screen"
      let some database := witness.value | throwError "not generated"
      if (← rejected.get).isNone then
        rejected.set (some database)
        throwError "rejected certificate"
      pure (value, database)
  let some (value, database) := accepted | throwError "the value 1 was not reached within 200 candidates"
  unless value == .integer 1 && (← rejected.get).any (·.raw != database.raw) do
    throwError "the search did not continue after the rejected candidate"

/-- Checks that {name}`Check.visitCandidates` screens the last candidate of a share inside the
timed task of compiled work: the screen never ends in practice, so the search can stop only at
the time limit. The empty database uses the first of the two candidates, so the second is the
last candidate, which the stop test of {name}`Sampling.candidates` does not screen. -/
def lastScreenTimed : TermElabM Unit := do
  let endless : Check.Screen := fun _ _ => Nat.fold 1000000000000 (fun index _ sum => sum + index) 0 == 1
  let stopped ← Check.withCompiledLimit 100 do
    let result ← Check.visitCandidates (mkConst ``True) { candidates := 2, screen := some endless }
      fun _ _ => (throwError "rejected certificate" : TermElabM Unit)
    pure (result.isNone && (← Check.compiledLimitExpired))
  unless stopped do throwError "the screen of the last candidate escaped the time limit"

/-- Checks that {name}`Check.visitCandidates` gives the empty database to the kernel only when
the screen accepts it: with a screen that accepts nothing, the callback, which certifies in the
checker, is never called. -/
def emptyScreened : TermElabM Unit := do
  let calls ← IO.mkRef (0 : Nat)
  discard <| Check.visitCandidates (mkConst ``True) { candidates := 10, screen := some fun _ _ => false }
    fun _ _ => do calls.modify (· + 1); (throwError "rejected certificate" : TermElabM Unit)
  unless (← calls.get) == 0 do throwError "the kernel got a candidate that the screen rejects"

elab "check_candidate_shares" : command => Command.liftTermElabM do
  emptyScreened
  valueShares
  lastScreenTimed
  logInfo "candidate shares passed"

set_option maxHeartbeats 10000000 in
check_candidate_shares

end CandidateSharesFixture
