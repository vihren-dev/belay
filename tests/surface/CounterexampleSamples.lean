import Belay
import Belay.Sqlite.SampleShrink
import Belay.Sqlite.CounterexampleShrink

open Belay.Sqlite Lean Elab Meta

/-! Our Plausible instances preserve validity, expose SQL boundary candidates, and retain
only kernel-certified counterexamples while shrinking under a finite attempt budget. -/

#check (inferInstance : Plausible.SampleableExt Value)
#check (inferInstance : Plausible.SampleableExt Database)

/-- A constrained base distinguishes valid sampling from unchecked row generation. -/
def constrained : Database := db! "CREATE TABLE t(a INTEGER NOT NULL UNIQUE); INSERT INTO t VALUES(7)"

/-- Three valid rows exceed the generator's bound; every nonempty default draw violates CHECK. -/
def oversized : Database := db! "CREATE TABLE t(a INTEGER NOT NULL CHECK(a = 7)); INSERT INTO t VALUES(7),(7),(7)"

/-- The schema makes ASCII case equal for grouping and keeps non-ASCII case distinct. -/
def nocase : Database := db! "CREATE TABLE t(x TEXT COLLATE NOCASE)"

/-- Integer affinity retains both positive operands that overflow SUM together. -/
def integers : Database := db! "CREATE TABLE t(x INTEGER)"

/-- Certify each generated database independently of its runtime validity proof. -/
def checkDatabase (database : Database) : MetaM Unit := do
  let expression := databaseExpr database.raw
  checkWithKernel expression

set_option maxHeartbeats 2000000 in
run_meta do
  let mut accepted := 0
  for seed in List.range 8 do
    if let .ok sample := Sampling.seeded (Sampling.database constrained) seed then
      accepted := accepted + 1
      unless sample.raw.rows.all (·.length ≤ 2) do throwError "sample exceeded its row bound"
      checkDatabase sample
      for smaller in Sampling.shrinkDatabase sample do checkDatabase smaller
  unless accepted > 0 do throwError "seeded generation rejected every candidate"
  let .ok empty := Sampling.seeded (Sampling.database constrained (maxRows := 0))
    | throwError "zero-row sampling failed"
  unless empty.raw.rows.all List.isEmpty do throwError "zero-row bound was ignored"
  let mut rejected := false
  for seed in List.range 8 do
    match Sampling.seeded (Sampling.database oversized (maxRows := 1)) seed with
    | .error _ => rejected := true
    | .ok sample =>
      unless sample.raw.rows.all (·.length ≤ 1) do throwError "rejected rows returned the oversized base"
  unless rejected do throwError "constraint rejection was not exercised"
  for sample in Sampling.targeted nocase ++ Sampling.targeted integers do checkDatabase sample
  unless (Sampling.schema [("t", [])]).isNone do throwError "invalid schema was accepted"
  unless (Sampling.validated { rows := [[]] }).isNone do throwError "invalid raw database was accepted"
  logInfo "generated and shrunk databases certified"

/-- Try the common candidate/certificate boundary over a finite explicit sequence. -/
def firstRefutation (proposition : Expr) (candidates : List Database) : MetaM Expr := do
  for candidate in candidates do
    try
      return ← Check.refuteWitness proposition { database := databaseExpr candidate.raw }
    catch _ => pure ()
  throwError "the targeted sequence did not refute its claim"

/-- False claim: every database with the exact ASCII rows under NOCASE has no duplicate group. -/
def asciiClaim : Prop := ∀ database : Database,
  database.raw.catalog = nocase.raw.catalog →
  database.rows "t" = some [[Value.text [97]], [Value.text [65]]] →
  Empty (sql "SELECT x FROM t GROUP BY x HAVING COUNT(*) > 1") database

/-- False claim: every database with the exact non-ASCII case rows under NOCASE has a duplicate group. -/
def unicodeClaim : Prop := ∀ database : Database,
  database.raw.catalog = nocase.raw.catalog →
  database.rows "t" = some [[Value.text "æ".toUTF8.toList], [Value.text "Æ".toUTF8.toList]] →
  Holds (sql "SELECT 1 FROM t GROUP BY x HAVING COUNT(*) > 1") database

/-- False claim: every database with the exact positive integer pair has a nonfailing SUM. -/
def overflowClaim : Prop := ∀ database : Database,
  database.raw.catalog = integers.raw.catalog →
  database.rows "t" = some [[Value.integer 4611686018427387904], [Value.integer 4611686018427387904]] →
  ¬ Fails (sql "SELECT SUM(x) FROM t") database

set_option maxHeartbeats 2000000 in
run_meta do
  discard <| firstRefutation (mkConst ``asciiClaim) (Sampling.targeted nocase)
  logInfo "ASCII NOCASE duplicate certified"
  discard <| firstRefutation (mkConst ``unicodeClaim) (Sampling.targeted nocase)
  logInfo "non-ASCII case distinction certified"
  discard <| firstRefutation (mkConst ``overflowClaim) (Sampling.targeted integers)
  logInfo "integer SUM overflow certified"

/-- The claim that every database lacks t has both large and smaller witnesses. -/
def missingTableClaim : Prop := ∀ database : Database, database.rows "t" = none

set_option maxHeartbeats 2000000 in
run_meta do
  let proposition := mkConst ``missingTableClaim
  let initial : Check.Witness := { database := databaseExpr constrained.raw }
  let smaller : Check.Witness := { database := databaseExpr integers.raw }
  let invalid : Check.Witness := { database := databaseExpr { rows := [[]] } }
  let empty : Check.Witness := { database := mkConst ``Database.empty }
  let (result, proof) ← Check.shrinkCertified proposition initial (fun _ => pure [invalid, empty, smaller]) 3
  unless result.database == smaller.database do throwError "shrinking retained an unconfirmed candidate"
  discard <| Check.certify (mkNot proposition) proof
  let calls ← IO.mkRef (0 : Nat)
  let (_, repeatedProof) ← Check.shrinkCertified proposition initial (fun witness => do
    calls.modify (· + 1)
    pure [witness]) 5
  unless (← calls.get) == 5 do throwError "shrinking did not enforce its total attempt bound"
  discard <| Check.certify (mkNot proposition) repeatedProof
  logInfo "bounded shrinking recertified"
