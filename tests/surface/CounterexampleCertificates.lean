import Belay
import Belay.Sqlite.SqlRefute

open Belay.Sqlite Lean Elab Meta

/-! The SQL witness boundary must certify the exact claim and reject forged, admitted,
native-decision and self-dependent evidence. No sampling result is trusted here. -/

namespace CertificateFixture

theorem missingTable : ¬ (∀ db : Database, Holds (sql "SELECT 1 FROM absent") db) := by
  sql_refute (db := Database.empty)

theorem checkedPrecondition : ¬ (∀ db : Database, True → Empty (sql "SELECT 1") db) := by
  sql_refute (db := Database.empty)

theorem parameter : ¬ (∀ amount : Value, ∀ db : Database,
    Empty ((sql "SELECT :amount") amount) db) := by
  sql_refute (db := Database.empty) (amount := (Value.integer 7))

theorem successFailure : ¬ Succeeds (sql "INSERT INTO absent VALUES (1)") (fun _ => True) := by
  sql_refute (db := Database.empty)

/-- Two possible results distinguish canonical execution from universal success. -/
def sample : Database := db! "CREATE TABLE t(x INTEGER); INSERT INTO t VALUES (1), (2)"

/-- The canonical first row succeeds; the other permitted row selects a failing query. -/
def alternativeFails : Sql (List Output) := do
  match ← single (sql "SELECT x FROM t LIMIT 1") with
  | some (.integer 1) => pure []
  | _ => send (sql "SELECT x FROM missing")

example : (sample.run alternativeFails Check.candidateEnvironment).outputs.allOk = true := by decide +kernel

theorem alternativeFailure : ¬ Succeeds alternativeFails (fun db => (db.rows "t").isSome = true) := by
  sql_refute (db := sample)

/-- The actual oneOf wrapper fails even though every concrete rows continuation succeeds. -/
def actualFails : Sql (List Output) :=
  let (statement, values) := (sql "SELECT x FROM t LIMIT 1").statements[0]
  .exec statement values fun output => match output with
    | .oneOf _ => send (sql "SELECT x FROM missing")
    | _ => .pure []

theorem actualFailure : ¬ Succeeds actualFails (fun db => (db.rows "t").isSome = true) := by
  sql_refute (db := sample)

theorem checkedClaim : True := True.intro
theorem indirectClaim : True := checkedClaim
theorem nativeClaim : True := by native_decide
axiom forged : False
def indirectForged : False := forged
unsafe def unsafeProof : False := unsafeCast True.intro
unsafe def indirectUnsafe : False := unsafeProof

/-- Fail the fixture if a malformed candidate passes the public certification boundary. -/
def rejects (action : MetaM Expr) : MetaM Unit := do
  let accepted ← try discard action; pure true catch _ => pure false
  if accepted then throwError "the SQL certificate boundary accepted a forbidden candidate"

run_meta do
  discard <| Check.certify (mkConst ``True) (mkConst ``True.intro)
  rejects <| Check.certify (mkConst ``False) (mkConst ``True.intro)
  rejects <| Check.certify (mkConst ``False) (mkConst ``indirectForged)
  rejects <| Check.certify (mkConst ``False) (mkConst ``unsafeProof)
  rejects <| Check.certify (mkConst ``False) (mkConst ``indirectUnsafe)
  rejects <| Check.certify (mkConst ``True) (mkConst ``nativeClaim)
  rejects <| Check.certify (mkConst ``True) (mkConst ``indirectClaim) #[``checkedClaim]
  let admitted ← mkSorry (mkConst ``Database) true
  rejects <| Check.refuteWitness (mkConst ``False) { database := admitted }
  let invalid := databaseExpr { rows := [[]] }
  rejects <| Check.refuteWitness (mkConst ``False) { database := invalid }
  rejects <| Check.refuteWitness (mkConst ``False) { database := mkNatLit 0 }
  rejects <| Check.refuteWitness (mkConst ``False)
    { database := mkConst ``Database.empty, environment := mkNatLit 0 }
  withLocalDeclD `assumed (mkConst ``True) fun assumed => do
    rejects <| Check.certify (mkConst ``True) assumed #[] #[assumed.fvarId!]

example : True := by
  fail_if_success
    have : ¬ (∀ db : Database, False → Empty (sql "SELECT 1") db) := by
      sql_refute (db := Database.empty)
  trivial

example : True := by
  fail_if_success
    have : ¬ Succeeds (sql "SELECT CURRENT_TIMESTAMP") (fun _ => True) := by
      sql_refute (db := Database.empty) (env := Env.default)
  trivial

#print axioms missingTable
#print axioms checkedPrecondition
#print axioms parameter
#print axioms successFailure
#print axioms alternativeFailure
#print axioms actualFailure

end CertificateFixture
