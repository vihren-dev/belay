import Belay.Sqlite.Programs.Automation.SqlRunGoals
import Belay.Sqlite.Programs.Scripts.KindRuleSend
import Belay.Sqlite.Model.Programs.Scripts.PlainInsertRule

set_option doc.verso true

/-! The path of {lit}`sql_run` through the kind rules (statement rule pilot). A kind rule of the model is a theorem
in the simp set {lit}`step_rule` that gives the step of every statement of its kind. The tactic applies
{lit}`Sql.check_send_of_rule` with the first kind rule whose resolution premise the hints close, and splits the
step that the rule gives on its cases. A hint that rewrites the subject of a match to one pattern, such as the
table at a position, selects that case instead of a split. The path has no table of kinds: a new kind rule in the set is used without
a change here. A wrong rule only makes the application fail, so the path cannot prove a false goal. -/

namespace Belay.Sqlite.Run
open Lean Meta Elab Tactic

/-- The names of the kind rules: the theorems in the simp set {lit}`step_rule`, in the order of their names. -/
def kindRuleNames : CoreM (List Name) := do
  let some extension ← getSimpExtension? `step_rule | return []
  let theorems ← extension.getTheorems
  let names := theorems.lemmaNames.fold (init := []) fun names origin =>
    match origin with
    | .decl name .. => name :: names
    | _ => names
  return names.toArray.qsort (·.lt ·) |>.toList

/-- The goal {lit}`RunStep.Continuing property result` with the match {lit}`result` reduced by a hint: the first
hint that rewrites the goal so that the match takes one alternative, for example an equation that gives the table
at a position. The result is {lean}`none`, and the goal is unchanged, when no hint does this. -/
def reduceMatchByHint (hints : Hints) (goal : MVarId) : TacticM (Option MVarId) := goal.withContext do
  for hint in hints do
    let saved ← Tactic.saveState
    try
      setGoals [goal]
      evalTactic (← `(tactic| rewrite (config := { transparency := .default }) [$hint:term]))
      let rewritten ← getMainGoal
      let target ← instantiateMVars (← rewritten.getType)
      if let .reduced alternative ← reduceMatcher? target.appArg! then
        return some (← rewritten.replaceTargetDefEq (mkApp target.appFn! alternative.headBeta))
    catch _ => pure ()
    saved.restore
  return none

/-- Split a goal {lit}`RunStep.Continuing property result` on the cases of {lit}`result`, after the local
definitions and the annotations of the goal are removed: a condition with {name}`Model.RunStep.continuing_ite`,
and a pattern match by the hints ({name}`reduceMatchByHint`) or else by its splitter. A case that ends the run
requires nothing and is closed. A case that continues with an output that is no choice and with no further
execution becomes, through {name}`Sql.sendReached_single`, the post at the reached context, with the hypothesis
{lit}`valid` on the reached connection; its tag is {lit}`failure` for an error output and {lit}`success` for any
other output. Any other goal is returned unchanged. -/
partial def ruleCases (hints : Hints) (goal : MVarId) : TacticM (List MVarId) := goal.withContext do
  let target ← zetaReduce (← instantiateMVars (← goal.getType))
  let target ← Meta.transform target (pre := fun e => return if e.isMData then .visit e.consumeMData else .continue)
  let goal ← goal.replaceTargetDefEq target
  unless target.isAppOfArity ``Model.RunStep.Continuing 2 do return [goal]
  let result := target.appArg!
  let condition := mkIdent `condition
  if result.isAppOfArity ``ite 5 then
    setGoals [goal]
    evalTactic (← `(tactic| refine Model.RunStep.continuing_ite (fun $condition => ?_) (fun $condition => ?_)))
    let cases ← getGoals
    return (← cases.mapM (ruleCases hints)).flatten
  if result.isAppOf ``Model.RunStep.ended then
    setGoals [goal]
    evalTactic (← `(tactic| exact trivial))
    return []
  if result.isAppOfArity ``Model.RunStep.continued 3 then
    let output := result.getArg! 0
    try
      setGoals [goal]
      evalTactic (← `(tactic| refine Sql.sendReached_single (by intro _ same; cases same) fun $(mkIdent `valid) => ?_))
      let leaf ← getMainGoal
      leaf.setTag (if output.isAppOf ``Model.Output.error then `failure else `success)
      return [leaf]
    catch _ => return [goal]
  if (← isMatcherApp result) then
    if let .reduced alternative ← reduceMatcher? result then
      return ← ruleCases hints (← goal.replaceTargetDefEq (mkApp target.appFn! alternative.headBeta))
    if let some reduced ← reduceMatchByHint hints goal then return ← ruleCases hints reduced
    let cases ← Split.splitMatch goal result
    return (← cases.mapM (ruleCases hints)).flatten
  return [goal]

/-- Close the premise {lit}`modeled` of {name}`Sql.check_send_of_rule` from the hints and the hypotheses. When they
do not close it, {name}`Model.RunStep.continues_of_rule` carries it over the kind rule {lit}`rule` to the step
itself, and the hints and the hypotheses get one more attempt. The result is the premise that stays open, with the
tag {lit}`modeled`: about the step when the carry-over applies, else unchanged. -/
def closeModeled (hints : Hints) (rule : Expr) (goal : MVarId) : TacticM (List MVarId) := do
  if ← closeSide hints `modeled goal then return []
  let saved ← Tactic.saveState
  try
    setGoals [goal]
    evalTactic (← `(tactic| refine Model.RunStep.continues_of_rule $(← Term.exprToSyntax rule) ?_))
    let step ← getMainGoal
    step.setTag `modeled
    if ← closeSide hints `modeled step then return []
    return [step]
  catch _ =>
    saved.restore
    return [goal]

/-- Apply the first kind rule whose resolution premise the hints or the hypotheses close, through
{name}`Sql.check_send_of_rule`. The result is the open premises with the open variables of the rule, and the
cases of the step that continue ({name}`ruleCases`). The result is {lean}`none`, and the goal is unchanged, when no
kind rule fits. -/
def applyKindRule (hints : Hints) (goal : MVarId) : TacticM (Option (List MVarId × List MVarId)) := do
  for rule in ← kindRuleNames do
    let saved ← Tactic.saveState
    try
      setGoals [goal]
      evalTactic (← `(tactic| refine' Sql.check_send_of_rule ?rule ?valid ?modeled ?reached))
      let goals ← getGoals
      let tagged (name : Name) : TacticM (List MVarId) :=
        goals.filterM fun new => return (← new.getTag).eraseMacroScopes == name
      let some equation := (← tagged `rule).head? | throwError "sql_run: the bridge has no rule premise"
      setGoals [equation]
      evalTactic (← `(tactic| refine' $(mkIdent rule) ?found))
      let ruleGoals ← getGoals
      let some found := (← ruleGoals.filterM fun new => return (← new.getTag).eraseMacroScopes == `found).head?
        | throwError "sql_run: the kind rule {rule} has no resolution premise"
      unless ← closeSide hints `found found do throwError "sql_run: no hint closes the resolution for {rule}"
      let ruleProof ← instantiateMVars (mkMVar equation)
      let mut open_ := []
      for premise in ← tagged `valid do
        unless ← closeSide hints `valid premise do open_ := open_ ++ [premise]
      for premise in ← tagged `modeled do open_ := open_ ++ (← closeModeled hints ruleProof premise)
      let mut cases := []
      for reached in ← tagged `reached do cases := cases ++ (← ruleCases hints reached)
      let premises := [`rule, `found, `valid, `modeled, `reached]
      let variables ← (goals ++ ruleGoals).filterM fun new => do
        return !premises.contains (← new.getTag).eraseMacroScopes && !(← new.isAssigned)
      return some (variables ++ open_, cases)
    catch _ => saved.restore
  return none

end Belay.Sqlite.Run
