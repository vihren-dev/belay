import Belay.Sqlite.Tooling.Counterexamples.CheckBudget
import Belay.Sqlite.Programs.Automation.AutoSearch

set_option doc.verso true

/-! The search of {lit}`sql_auto` (ADR 0017, S6; ADR 0027, D6). The search tries four routes in a fixed
order: {lit}`sql_commute`, {lit}`sql_run` with the finishing steps of the SQL simp set, {lit}`sql_select`
and {lit}`grind`. Each route runs
on the goal alone, with the work limit of its share, and without error recovery, so a failed step never
becomes a hidden {lit}`sorry`. A route that fails leaves the goal and the state as they were. The result is
the list of explicit tactic steps of the route that closed the goal, so a caller can offer them as a proof
that does not search again. A proof that the search builds is checked by the kernel like any other proof. -/

namespace Belay.Sqlite.Run
open Lean Meta Elab Term Tactic

/-- Search the routes in order for a proof of the goal. The work limit of the call is shared by the routes
that have not run yet. A route that fails, runs out of its share, or builds an incomplete proof leaves
the goal and the state as they were, and its reason goes into the error. -/
def search (hints : Array (TSyntax `term)) (goal : MVarId) : TermElabM (Except String Found) := do
  let mut reasons : Array String := #[]
  let mut left := Route.all.length
  for route in Route.all do
    let share := (← Check.remainingUnits) / left
    left := left - 1
    try
      let outcome ← Check.withinBudget share do
        let steps ← runRoute hints goal route
        unless ← completeProof goal do throwError "its proof is incomplete."
        return steps
      match outcome with
      | some steps => return .ok { route, steps }
      | none => reasons := reasons.push s!"- {route.label}: it used the work limit of its share."
    catch error =>
      let text ← error.toMessageData.toString
      reasons := reasons.push s!"- {route.label}: {(text.splitOn "\n").head!}"
  return .error ("\n".intercalate reasons.toList)

end Belay.Sqlite.Run
