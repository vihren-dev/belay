import Belay.Sqlite.Programs.Automation.AutoSearch
import Lean.Meta.Tactic.TryThis

set_option doc.verso true

namespace Belay.Sqlite.Run
open Lean Meta Elab Term Tactic

/-- Try the routes {lit}`sql_commute`, {lit}`sql_run`, {lit}`sql_select` and {lit}`grind` in this order on the main
goal, with the hints of the call. The routes are explicit tactics too, so a user can run each one alone. The tactic fails
with the reason of each route when none closes the goal, and the goal and the other goals stay as they were.
When a route closes the goal, the editor offers the steps of that route as a replacement of this call. -/
syntax (name := sqlAuto) "sql_auto" (" [" term,* "]")? : tactic

/-- Offer the steps as the replacement of the call syntax. The text puts each step on its own line at the
column of the call, so the replaced proof keeps the layout of the proof around it. -/
def suggestSteps (title : String) (stx : Syntax) (steps : Array (TSyntax `tactic)) : TacticM Unit := do
  let some range := stx.getRange? | return
  let (_, column) := Meta.Tactic.TryThis.getIndentAndColumn (← getFileMap) range
  let lines ← steps.mapM fun step => do
    return (← PrettyPrinter.ppTactic step).pretty
  let text := ("\n".pushn ' ' column).intercalate lines.toList
  Meta.Tactic.TryThis.addSuggestion stx { suggestion := .string text, toCodeActionTitle? := some fun _ => title }
    (origSpan? := stx) (header := title ++ ":")

end Belay.Sqlite.Run
