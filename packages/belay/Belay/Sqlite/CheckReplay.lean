import Belay.Sqlite.CheckClaim
import Belay.Sqlite.CounterexampleShrink
import Belay.Sqlite.SampleShrink
import Belay.Sqlite.CheckReplayData

set_option doc.verso true

/-! Replay acceptance for a certified candidate. SQL sites come from the original proposition
at its checked inputs; unsupported SQL never falls back to a fictitious plain-Lean query. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term

/-- The note of a report for a program that runs Lean code, for a report that runs the first scripts. -/
def leanCodeNote : String :=
  "The program runs Lean code after the scripts of this replay, so SQLite did not run the whole program. " ++
  "The model's run of the whole program gives the failing result."

/-- The note of a report that builds the database only, for a program with no script to replay. -/
def noScriptNote : String :=
  "The program is Lean code, or it sends no script that this replay can run. The replay builds the database only. " ++
  "The model's run of the program gives the failing result."

/-- Reconstruct every recognized query observation in the instantiated claim. A plain Lean
predicate receives only its database reconstruction. SQL outside the supported structural
query/script forms, unavailable observations, or missing original text refuse the report.
The caller separately supplies the certified refutation of the original proposition. -/
def replayClaim (proposition : Expr) (witness : Witness)
    (excluded : Array Name := #[]) (excludedLocals : Array FVarId := #[]) :
    TermElabM (Array Replay.Report) := do
  let sites ← querySites proposition witness.choose witness.database
  if sites.unsupported then throwError "SQL replay is unavailable for this claim's structure"
  if sites.sites.isEmpty then
    unless sites.leanCode || (← sqlMention? proposition (includeSource := false)) == some false do
      throwError "SQL replay could not identify the original query and its database"
    let construction ← checkedConstruction witness.database excluded excludedLocals
    return #[{ construction, sqlite := construction ++ "\n;\n", note := if sites.leanCode then some noScriptNote else none }]
  let reports ← sites.sites.mapM fun site => checkedScriptReport site.database site.script
    (excluded := excluded) (excludedLocals := excludedLocals)
  return if sites.leanCode then reports.map ({ · with note := some leanCodeNote }) else reports

/-- Raw results of the existing validity-preserving shrinker. The background caller reduces
this computation cooperatively; every retained proposal still needs a fresh certificate. -/
def smallerData (database : Database) : List Database.Raw :=
  (Sampling.shrinkDatabase database).map (·.raw)

/-- Use the shared validity-preserving database shrinker without changing named inputs or
its environment. These are proposals only; {name}`shrinkCertified` must recertify a retained
candidate. Callers can supply other proposal functions to that primitive. -/
def shrinkProposals (witness : Witness) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM (List Witness) := do
  let smaller ← dataValue (List Database.Raw) (mkApp (mkConst ``smallerData) witness.database)
    excluded excludedLocals
  return smaller.map fun raw => { witness with database := databaseExpr raw }

end Belay.Sqlite.Check
