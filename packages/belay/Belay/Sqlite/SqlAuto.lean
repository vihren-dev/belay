import Belay.Sqlite.AutoSearch
import Lean.Meta.Tactic.TryThis

set_option doc.verso true

/-! The tactic {lit}`sql_auto` (ADR 0017, S6). It runs the search of {lit}`Belay.Sqlite.AutoSearch` and, when the
search closes the goal, offers the explicit steps of the winning route as a replacement for the call. The
replacement names the rules that the route used and runs the same steps in the same goal, so it proves the
goal again without a search. -/

namespace Belay.Sqlite.Run
open Lean Meta Elab Term Tactic

/-- Try the routes {lit}`sql_commute`, {lit}`sql_run` and {lit}`grind` in this order on the main goal, with the
hints of the call. The routes are explicit tactics too, so a user can run each one alone. The tactic fails
with the reason of each route when none closes the goal, and the goal and the other goals stay as they were.
When a route closes the goal, the editor offers the steps of that route as a replacement of this call. -/
syntax (name := sqlAuto) "sql_auto" (" [" term,* "]")? : tactic

/-- Offer the steps as the replacement of the call syntax. The text puts each step on its own line at the
column of the call, so the replaced proof keeps the layout of the proof around it. -/
def suggestSteps (stx : Syntax) (steps : Array (TSyntax `tactic)) : TacticM Unit := do
  let some range := stx.getRange? | return
  let (_, column) := Meta.Tactic.TryThis.getIndentAndColumn (← getFileMap) range
  let lines ← steps.mapM fun step => do
    return (← PrettyPrinter.ppTactic step).pretty
  let text := ("\n".pushn ' ' column).intercalate lines.toList
  Meta.Tactic.TryThis.addSuggestion stx { suggestion := .string text } (origSpan? := stx)

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
    suggestSteps stx found.steps

end Belay.Sqlite.Run
