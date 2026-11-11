import Belay

open Belay.Sqlite Lean Meta Elab
set_option maxHeartbeats 2000000

/-! Both tactic forms certify the original goal. A custom generator supplies ordinary
witness proposals through the public API, without relying on command syntax. -/

/-- The searched form finds SELECT 1's row. -/
theorem searched : ¬ (∀ db : Database, Empty (sql "SELECT 1") db) := by sql_refute

set_option sql.checkBudget 0 in
/-- The explicit primitive remains independent of disabled search options. -/
theorem supplied : ¬ (∀ db : Database, Empty (sql "SELECT 1") db) := by
  sql_refute (db := Database.empty)

/-- An explicit schema guides a plain Lean predicate with no SQL source to infer. -/
theorem schemaSearch : ¬ (∀ db : Database, db.rows "custom" = none) := by
  sql_refute with (schema := db! "CREATE TABLE custom(x);")

/-- A named binder called schema remains usable independently of the schema option. -/
theorem namedSearch : ¬ (∀ schema : Nat, ∀ _db : Database, schema = 0) := by
  sql_refute with (input schema := 7)

/-- The supplied unknown counter refutes the claim that every environment and database
starts with a known zero changes counter. The default complete environment cannot refute it. -/
theorem environmentSearch : ¬ (∀ environment : Env, ∀ _db : Database,
    environment.counters.changes = some 0) := by
  sql_refute with (env := Env.default)

/-- info: SQL check: unknown; no proof or replayable counterexample was found within the budget. -/
#guard_msgs in
set_option sql.checkCandidates 1 in
#sql_check Succeeds (sql "INSERT INTO absent VALUES (1)") (fun _ => True)
  with (db := Database.empty) (env := Env.default)

/-- Exhaustion leaves the tactic goal intact, so an ordinary proof can follow. -/
theorem afterUnknown : ¬ False := by
  fail_if_success (set_option sql.checkBudget 0 in sql_refute)
  intro h
  exact h

/-- A goal outside negation is rejected without assignments. -/
theorem wrongGoal : True := by
  fail_if_success sql_refute
  trivial

/-- This witness cannot refute reflexivity; search failure supplies no proof. -/
theorem trueClaim : (∀ db : Database, db = db) := by
  fail_if_success (have : ¬ (∀ db : Database, db = db) := by sql_refute)
  intro db
  rfl

/-- An incorrect explicit witness is rejected before the valid witness is checked. -/
theorem afterBadWitness : ¬ (∀ db : Database, db.rows "custom" = none) := by
  fail_if_success (set_option sql.checkCandidates 1 in
    sql_refute with (db := Database.empty))
  sql_refute (db := db! "CREATE TABLE custom(x);")

/-- Users can compute candidate sequences in Lean's elaboration monad. -/
def customCandidates : Term.TermElabM (Array Check.Witness) := do
  return #[{ database := mkConst ``Database.empty }]

/-- A plain predicate needs no recognized SQL site to use the flexible checking API. -/
def noDatabase : Prop := ∀ _db : Database, False

elab "check_custom_candidates" : command => Command.runTermElabM fun _ => do
  let outcome ← Check.check (mkConst ``noDatabase) 100000
    { witnesses := ← customCandidates, candidates := 1 }
  let .refuted _ proof := outcome.result | throwError "the custom candidates did not reach certification"
  discard <| Check.certify (mkNot (mkConst ``noDatabase)) proof
  unless !outcome.replays.isEmpty && outcome.replays.all (·.original.isNone) do
    throwError "the plain predicate was presented as an SQL query"
  logInfo "custom candidates certify the original plain predicate"

check_custom_candidates

/-- The native command context must forward its cancellation token through runTermElabM. -/
elab "check_frontend_cancellation" : command => do
  let token ← IO.CancelToken.new
  token.set
  let _ : MonadExceptOf Exception Command.CommandElabM := MonadAlwaysExcept.except
  let interrupted ← try
    withReader (fun context => { context with cancelTk? := some token }) <|
      Belay.Sqlite.elabSqlCheckCommand (← `(command| #sql_check True))
    pure false
  catch error =>
    if error.isInterrupt then pure true else throw error
  unless interrupted do throwError "the command swallowed cancellation"
  logInfo "frontend command cancellation propagated"

check_frontend_cancellation
#sql_check True

#print axioms searched
#print axioms supplied
#print axioms schemaSearch
#print axioms namedSearch
#print axioms environmentSearch
#print axioms afterUnknown
#print axioms wrongGoal
#print axioms trueClaim
#print axioms afterBadWitness
