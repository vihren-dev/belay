import SelectProcedureCases
import S6CheckLabels

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_select_procedure_test.py`: background checking
({lit}`#sql_check`) of claims about the results of a SELECT (B10). The checker proves the A01 claim
through the route {lit}`sql_select` of its search; it refutes false claims about a run with a database
from the screen of the schema, an explicit database, a database that the claim names and the empty
database, each with a SQLite replay; it screens and refutes a convenience claim; and it answers
unknown, with the reason, for a true claim that the procedure cannot prove and for a refutation without
a replay. The checks at the end call the checking API: an excluded rule removes the proof, and a
cancellation inside the search gives no result. -/

set_option maxHeartbeats 4000000
set_option sql.check false

namespace SelectCheckCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectProjectionCases
open Lean Meta Elab

labelled_sql "select-proved" in
#sql_check ∀ (db : Database) (env : Env), db.HasCatalog invoices →
  (db.run (query customerOfFirst customerOfFirst_one) env).returnsRows firstCellPresent

labelled_sql "convenience-screened" in
#sql_check ∀ db : Database, db.HasCatalog invoices → Empty customerOfFirst db

labelled_sql "run-schema-false" in
#sql_check ∀ (db : Database) (env : Env), db.HasCatalog invoices →
  (db.run (query customerOfFirst customerOfFirst_one) env).returnsResult (· = []) with (schema := invoices)

labelled_sql "run-witness-false" in
#sql_check ∀ (db : Database) (env : Env), db.HasCatalog invoices →
  (db.run (query customerOfFirst customerOfFirst_one) env).returnsResult (· = []) with (db := shop)

labelled_sql "run-named-false" in
#sql_check ∀ (db : Database) (env : Env), db = shop →
  (db.run (query customerOfFirst customerOfFirst_one) env).returnsResult (· = [])

labelled_sql "run-empty-false" in
#sql_check ∀ (db : Database) (env : Env),
  (db.run (query customerOfFirst customerOfFirst_one) env).returnsRows firstCellPresent

labelled_sql "arithmetic-unknown" in
#sql_check ∀ (db : Database) (env : Env), db.HasCatalog SelectGroupCases.orders →
  (db.run (query SelectCountCases.countAll SelectCountCases.countAll_one) env).returnsResult
    (· = [[.integer ((db.scanAt 0).length ^ 2 / (db.scanAt 0).length)]])

/- The run of {name}`Sql.run` is no {name}`Database.run`, so the checker finds no script to replay. -/
set_option sql.checkCandidates 2 in
labelled_sql "replay-unknown" in
#sql_check ∀ (db : Database) (env : Env),
  ((query customerOfFirst customerOfFirst_one).run db env).returnsRows firstCellPresent

/-- The A01 claim: for every database with the catalog of {name}`invoices` and every environment, the
query {name}`customerOfFirst` returns a result whose rows each have a first cell that is not NULL. -/
def selectClaim : Prop := ∀ (db : Database) (env : Env), db.HasCatalog invoices →
  (db.run (query customerOfFirst customerOfFirst_one) env).returnsRows firstCellPresent

/-- The statement of {name}`selectClaim`, which the opening of the search introduces. -/
def selectStatement : MetaM Expr := return (← getConstInfo ``selectClaim).value!

/-- The proof route of the checker, with no candidates: it proves {name}`selectClaim`, and with its
execution rule {name}`Run.query_returnsResult_ofCatalog` excluded, the audit refuses the proof that uses
the rule, so the result is unknown. -/
def excludedRule : TermElabM Unit := do
  let statement ← selectStatement
  let .proved _ ← Check.checkCandidates statement (pure #[]) Check.defaultProof
    | throwError "the checker did not prove the A01 claim"
  let .unknown ← Check.checkCandidates statement (pure #[]) Check.defaultProof
      #[``Run.query_returnsResult_ofCatalog]
    | throwError "the checker proved the A01 claim with its execution rule excluded"
  logInfo "excluded rule: unknown"

#eval excludedRule

/-- A cancellation during the search of the proof: the cheap closing tactics fail on
{name}`selectClaim`, then the token is set and the search starts. The check must pass the interruption on
with no result, and the elaboration must keep no message of the check. -/
def cancelledSearch : TermElabM Unit := do
  let statement ← selectStatement
  let token ← IO.CancelToken.new
  let messages := (← getThe Core.State).messages.toList.length
  let searched ← IO.mkRef false
  let prove (proposition : Expr) : TermElabM (Option Check.Proven) := do
    if let some proven ← Check.tryProof proposition then return some proven
    token.set
    searched.set true
    Check.searchedProof proposition
  -- Only this check catches the interruption that the checking API must pass on.
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  let interrupted ← try
      discard <| withTheReader Core.Context (fun context => { context with cancelTk? := some token }) <|
        Check.check statement 200000 (prove := prove)
      pure false
    catch error => if error.isInterrupt then pure true else throw error
  unless interrupted && (← searched.get) && (← getThe Core.State).messages.toList.length == messages do
    throwError "the cancelled check did not pass the interruption on without a result"
  logInfo "cancelled search: interrupted"

#eval cancelledSearch

end SelectCheckCases
