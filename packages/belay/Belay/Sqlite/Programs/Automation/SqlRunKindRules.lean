import Belay.Sqlite.Programs.Automation.SqlRunGoals
import Belay.Sqlite.Programs.Scripts.KindRuleSend
import Belay.Sqlite.Model.Programs.Scripts.PlainInsertRule
import Belay.Sqlite.Model.Programs.Scripts.ResolvedStepGuards

set_option doc.verso true

/-! The path of {lit}`sql_run` through the kind rules (statement rule pilot). A kind rule of the model is a theorem
in the simp set {lit}`step_rule` that gives the step of every statement of its kind. The tactic applies
{lit}`Sql.check_send_of_rule` with the first kind rule whose resolution premise the hints close, and splits the
step that the rule gives on its cases. A hint that rewrites the subject of a match to one pattern, such as the
table at a position, selects that case instead of a split. The path has no table of kinds: a new kind rule in the set is used without
a change here. A wrong rule only makes the application fail, so the path cannot prove a false goal. -/

namespace Belay.Sqlite.Run
open Lean Meta Elab Tactic

/-- The names of the kind rules: the theorems in the simp set {lit}`step_rule`, in the order of their names. An
entry of the set that is no declaration, such as a local hypothesis, is no kind rule. -/
def kindRuleNames : CoreM (List Name) := do
  let some extension ← getSimpExtension? `step_rule | return []
  let theorems ← extension.getTheorems
  let names := theorems.lemmaNames.fold (init := []) fun names origin =>
    match origin with
    | .decl name .. => name :: names
    | .fvar _ | .stx .. | .other _ => names
  return names.toArray.qsort (·.lt ·) |>.toList

/-- Apply the theorem to the goal and return the new goals, each tagged with the name of its premise. The goal loses
its tag first, so that the tags of the new goals are the names alone. Unlike a named hole of {lit}`refine`, a tag
can repeat, so the tactic can apply the theorem to many statements of one program. -/
def applyTagged (goal : MVarId) (theorem_ : Name) : MetaM (List MVarId) := do
  goal.setTag .anonymous
  goal.apply (← mkConstWithFreshMVarLevels theorem_)

/-- The new goals whose tag is the name. The comparison ignores macro scopes, because a tag made from the name of a
premise can carry them, and the callers know only the name. -/
def taggedGoals (goals : List MVarId) (name : Name) : MetaM (List MVarId) :=
  goals.filterM fun new => return (← new.getTag).eraseMacroScopes == name

/-- The goal {lit}`RunStep.Continuing property result` with the match {lit}`result` reduced by a hint: the first
hint that rewrites the goal so that the match takes one alternative, for example an equation that gives the table
at a position. A rewrite that leaves a premise of the hint open is not used. The result is {lean}`none`, and the
goal is unchanged, when no hint does this. -/
def reduceMatchByHint (hints : Hints) (goal : MVarId) : TacticM (Option MVarId) := goal.withContext do
  for hint in hints do
    let saved ← Tactic.saveState
    try
      setGoals [goal]
      evalTactic (← `(tactic| rewrite (config := { transparency := .default }) [$hint:term]))
      let [rewritten] ← getGoals | throwError "sql_run: the hint leaves a premise open"
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
other output. Any other goal, such as a case with a choice between results, is returned unchanged. -/
partial def ruleCases (hints : Hints) (goal : MVarId) : TacticM (List MVarId) := goal.withContext do
  let target ← zetaReduce (← instantiateMVars (← goal.getType))
  let target ← Meta.transform target (pre := fun e => return if e.isMData then .visit e.consumeMData else .continue)
  let goal ← goal.replaceTargetDefEq target
  unless target.isAppOfArity ``Model.RunStep.Continuing 2 do return [goal]
  let result := target.appArg!
  if result.isAppOfArity ``ite 5 then
    let goals ← applyTagged goal ``Model.RunStep.continuing_ite
    let mut cases := []
    for side in (← taggedGoals goals `whenYes) ++ (← taggedGoals goals `whenNo) do
      let (_, side) ← side.intro `condition
      cases := cases ++ (← ruleCases hints side)
    return cases
  if result.isAppOf ``Model.RunStep.ended then
    setGoals [goal]
    evalTactic (← `(tactic| exact trivial))
    return []
  if result.isAppOfArity ``Model.RunStep.continued 3 then
    let output := result.getArg! 0
    let saved ← Tactic.saveState
    try
      let goals ← applyTagged goal ``Sql.sendReached_single
      let ([plain], [holds]) := (← taggedGoals goals `plain, ← taggedGoals goals `holds)
        | throwError "sql_run: the case of the kind rule has other premises"
      setGoals [plain]
      evalTactic (← `(tactic| (intro _ same; cases same)))
      unless (← getGoals).isEmpty do throwError "sql_run: the output can be a choice between results"
      let (_, leaf) ← holds.intro `valid
      leaf.setTag (if output.isAppOf ``Model.Output.error then `failure else `success)
      return [leaf]
    catch _ =>
      saved.restore
      return [goal]
  if (← isMatcherApp result) then
    if let .reduced alternative ← reduceMatcher? result then
      return ← ruleCases hints (← goal.replaceTargetDefEq (mkApp target.appFn! alternative.headBeta))
    if let some reduced ← reduceMatchByHint hints goal then return ← ruleCases hints reduced
    let cases ← Split.splitMatch goal result
    return (← cases.mapM (ruleCases hints)).flatten
  return [goal]

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
about the step when the carry-over applies, else unchanged. -/
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
    return [step]
  catch _ =>
    saved.restore
    return [goal]

/-- The premise of a kind rule that the resolution of the statement closes: the first new goal whose type is an
equation for {name}`Model.resolveStatement`. The name of the premise does not matter. -/
def resolutionPremise (goals : List MVarId) : MetaM (Option MVarId) :=
  goals.findM? fun new => do
    let some (_, side, _) := (← instantiateMVars (← new.getType)).eq? | return false
    return side.isAppOf ``Model.resolveStatement

/-- Apply the first kind rule whose resolution premise ({name}`resolutionPremise`) the hints or the hypotheses
close, through {name}`Sql.check_send_of_rule`. The result is the goals that stay open, and the cases of the step
that continue ({name}`ruleCases`). The goals that stay open are the premises of the bridge that the hints do not
close, and each other premise and variable of the rule that is not assigned. The result is {lean}`none`, and the
goal is unchanged, when no kind rule fits. -/
def applyKindRule (hints : Hints) (goal : MVarId) : TacticM (Option (List MVarId × List MVarId)) := do
  for rule in ← kindRuleNames do
    let saved ← Tactic.saveState
    try
      let goals ← applyTagged goal ``Sql.check_send_of_rule
      let tagged := taggedGoals goals
      let some equation := (← tagged `rule).head? | throwError "sql_run: the bridge has no rule premise"
      let ruleGoals ← applyTagged equation rule
      let some found ← resolutionPremise ruleGoals
        | throwError "sql_run: the kind rule {rule} has no resolution premise"
      unless ← closeSide hints `found found do throwError "sql_run: no hint closes the resolution for {rule}"
      let ruleProof ← instantiateMVars (mkMVar equation)
      let foundProof ← instantiateMVars (mkMVar found)
      let validPremises ← tagged `valid
      let modeledPremises ← tagged `modeled
      let reachedPremises ← tagged `reached
      let mut open_ := []
      for premise in validPremises do
        unless ← closeSide hints `valid premise do open_ := open_ ++ [premise]
      let validProof := (validPremises.head?.map mkMVar).getD (mkConst ``True.intro)
      for premise in modeledPremises do
        open_ := open_ ++ (← closeModeled hints ruleProof foundProof validProof premise)
      let mut cases := []
      for reached in reachedPremises do cases := cases ++ (← ruleCases hints reached)
      let handled := [equation, found] ++ validPremises ++ modeledPremises ++ reachedPremises
      let others ← (goals ++ ruleGoals).filterM fun new => return !handled.contains new && !(← new.isAssigned)
      return some (others ++ open_, cases)
    catch _ => saved.restore
  return none

end Belay.Sqlite.Run
