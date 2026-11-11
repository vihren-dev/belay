import Belay.Sqlite.Programs.Automation.SqlRun
import Belay.Sqlite.Programs.Automation.SqlCommute
import Belay.Sqlite.Queries.Evaluation.SqlSimpLaws

set_option doc.verso true

namespace Belay.Sqlite.Run
open Lean Meta Elab Term Tactic

/-- The routes of the search, in the order in which {lit}`sql_auto` tries them. -/
inductive Route where
  /-- The rules of preservation and commutation, with the hints of the call. -/
  | commute
  /-- The step rules, with the hints of the call, then one finishing step for each goal that stays. -/
  | run
  /-- The procedure of a SELECT, with the hints of the call: a claim about the results of a query, such as
  {lit}`returnsResult` or {lit}`returnsRows` of a run. -/
  | select
  /-- The grind tactic, with the hints of the call that name a declaration. Grind uses the local hypotheses by
  itself, so a hint that names one is left out. -/
  | grind

/-- The name of a route in messages. -/
def Route.label : Route → String
  | .commute => "sql_commute"
  | .run => "sql_run"
  | .select => "sql_select"
  | .grind => "grind"

/-- The routes in the order of the search. -/
def Route.all : List Route := [.commute, .run, .select, .grind]

/-- A closed search: the route that won and the explicit steps of its proof. -/
structure Found where
  /-- The route whose steps closed the goal. -/
  route : Route
  /-- The explicit steps that close the goal when they run again on it. -/
  steps : Array (TSyntax `tactic)

/-- Run one tactic on a goal, in a fresh goal list and without error recovery: an error in the tactic
fails the call, and the call returns the goals that the tactic leaves. -/
def runStrict (goal : MVarId) (script : TSyntax `tactic) : TermElabM (List MVarId) :=
  Term.withoutErrToSorry <| Tactic.run goal (Tactic.withoutRecover (evalTactic script))

/-- The steps that finish a goal that {lit}`sql_run` leaves, in the order in which they are tried: the
goal is a fact that holds by evaluation, by the SQL simp set, or by a decision in the kernel. -/
def finishingSteps : TermElabM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| · intros; rfl), ← `(tactic| · intros; trivial),
    ← `(tactic| · intros; simp [sql_simp]; done), ← `(tactic| · intros; decide +kernel)]

/-- The first finishing step that closes the goal, with the state after it. A step that fails leaves no
trace. -/
def finishGoal (goal : MVarId) : TermElabM (Option (TSyntax `tactic)) := do
  for step in ← finishingSteps do
    let saved ← saveState
    try
      if (← runStrict goal step).isEmpty then return some step
    catch _ => pure ()
    saved.restore
  return none

/-- Run one route on the goal. The result is the explicit steps that close the goal; the call fails with the
reason when the route does not close it. -/
def runRoute (hints : Array (TSyntax `term)) (goal : MVarId) : Route → TermElabM (Array (TSyntax `tactic))
  | .commute => do
    let step ← `(tactic| sql_commute [$hints,*])
    unless (← runStrict goal step).isEmpty do throwError "it left premises open."
    return #[step]
  | .run => do
    let step ← `(tactic| sql_run [$hints,*])
    let mut steps := #[step]
    for stays in ← runStrict goal step do
      let some finish ← finishGoal stays
        | throwError "it left a goal that rfl, trivial, simp [sql_simp] and decide do not close."
      steps := steps.push finish
    return steps
  | .select => do
    let step ← `(tactic| sql_select [$hints,*])
    unless (← runStrict goal step).isEmpty do throwError "it left a goal open."
    return #[step]
  | .grind => do
    let local_ ← goal.withContext getLCtx
    let lemmas := hints.filter fun hint => hint.raw.isIdent && (local_.findFromUserName? hint.raw.getId).isNone
    let names ← lemmas.mapM fun hint => `(Lean.Parser.Tactic.grindParam| $(⟨hint.raw⟩):ident)
    let step ← if names.isEmpty then `(tactic| grind) else `(tactic| grind [$names,*])
    unless (← runStrict goal step).isEmpty do throwError "it did not close the goal."
    return #[step]

/-- The proof of the goal must be complete: no metavariable and no {lit}`sorry` stay in it. -/
def completeProof (goal : MVarId) : TermElabM Bool := do
  let proof ← instantiateMVars (mkMVar goal)
  return !proof.hasExprMVar && !proof.hasSorry

end Belay.Sqlite.Run
