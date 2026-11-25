import Belay.Sqlite.Programs.Automation.SqlRunGoals
import Belay.Sqlite.Programs.Scripts.KindRuleSend

set_option doc.verso true

/-! Close the support obligation of a send using hints or the guards of its resolved statement. -/

namespace Belay.Sqlite.Run
open Lean Meta Elab Tactic

/-- Close the premise {lit}`modeled` of {name}`Sql.check_send_of_rule` with the guards of the step: when the
validity premise {lit}`valid` is closed, {name}`Model.step_guards_hold` gives the guards
({name}`Model.Resolved.Statement.StepGuards`) of the resolved statement {lit}`found`, and the attempt simplifies the
premise with them. The result tells whether the premise is closed; when it is not, the goal is unchanged. -/
def closeModeledByGuards (found valid : Expr) (goal : MVarId) : TacticM Bool := goal.withContext do
  let valid ← instantiateMVars valid
  if valid.hasExprMVar then return false
  let saved ← Tactic.saveState
  try
    setGoals [goal]
    withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic|
      (have guards := Belay.Sqlite.Model.step_guards_hold $(← Term.exprToSyntax found) rfl ($(← Term.exprToSyntax valid)).1
       simp only [Model.Resolved.Statement.StepGuards] at guards
       simp [Model.RunStep.continues, guards])))
    if (← getGoals).isEmpty then return true
  catch _ => pure ()
  saved.restore
  return false

/-- Close the premise {lit}`modeled` of {name}`Sql.check_send_of_rule`: from the hints and the hypotheses, then with
the guards of the step ({name}`closeModeledByGuards`). When neither closes it,
{name}`Model.RunStep.continues_of_rule` carries it over the kind rule {lit}`rule` to the step itself, and the hints
and the hypotheses get one more attempt. The result is the premise that stays open, with the tag {lit}`modeled`:
about the step when the carry-over applies, else unchanged. The open premise about the step has the kind rule as the
hypothesis {lit}`rule`, so that a proof can rewrite the step to its cases without the name of the step function. -/
def closeModeled (hints : Hints) (rule found valid : Expr) (goal : MVarId) : TacticM (List MVarId) := do
  if ← closeSide hints `modeled goal then return []
  if ← closeModeledByGuards found valid goal then return []
  let saved ← Tactic.saveState
  try
    setGoals [goal]
    evalTactic (← `(tactic| refine Model.RunStep.continues_of_rule $(← Term.exprToSyntax rule) ?_))
    let step ← getMainGoal
    step.setTag `modeled
    if ← closeSide hints `modeled step then return []
    let (_, step) ← (← step.assert `rule (← inferType rule) rule).intro1P
    step.setTag `modeled
    return [step]
  catch _ =>
    saved.restore
    return [goal]

end Belay.Sqlite.Run
