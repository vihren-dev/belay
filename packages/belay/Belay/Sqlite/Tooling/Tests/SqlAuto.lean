import Belay.Sqlite.Tooling.Tests.AutoSearch
import Belay.Sqlite.Programs.Automation.SqlAuto

set_option doc.verso true

/-! The tactic {lit}`sql_auto` (ADR 0017, S6). It runs the search of {lit}`Belay.Sqlite.AutoSearch` and, when the
search closes the goal, offers the explicit steps of the winning route as a replacement for the call. The
replacement names the rules that the route used and runs the same steps in the same goal, so it proves the
goal again without a search. -/

namespace Belay.Sqlite.Run
open Lean Meta Elab Term Tactic

/-- Run {lit}`sql_auto`: search for a proof of the main goal and, if one exists, close the goal and offer the
explicit steps as a suggestion in place of the call. -/
@[tactic sqlAuto] def evalSqlAuto : Tactic := fun stx => do
  let hints : Array (TSyntax `term) := match stx with
    | `(tactic| sql_auto [$hints,*]) => hints.getElems
    | _ => #[]
  let goal ← getMainGoal
  let siblings := (← getGoals).drop 1
  match ← search hints goal with
  | .error reasons =>
    throwError "sql_auto did not close the goal. The routes failed:\n{reasons}\nRun one of these tactics alone to see the goals that it leaves."
  | .ok found =>
    setGoals siblings
    suggestSteps "Replace sql_auto with its steps" stx found.steps

end Belay.Sqlite.Run
