import Belay.Sqlite.Programs.Automation.SqlSelectEval
import Belay.Sqlite.Queries.Automation.SqlSelectSteps

set_option doc.verso true

/-! The steps of the procedure of {lit}`sql_select`: closing a premise of a rule, applying a rule to the
goal (backward) and applying a rule to a hypothesis (forward). Each step changes the goal only by an
application of a proved theorem, so the kernel checks the proof that the procedure builds. A step that
fails leaves the goal and the metavariables as they were. -/

namespace Belay.Sqlite.Select
open Lean Meta Elab Tactic

/-- Close a premise of a rule. The attempts are, in order: evaluation by the kernel of an equation
whose left side is closed data, the hypotheses, each hint, {lit}`rfl`, {lit}`decide +kernel` for a
premise without variables, and the simplifier with the evaluation laws ({lit}`sql_select_simp`) for a
premise without metavariables. The hypotheses come before the hints: in a premise with a metavariable,
such as the catalog in {lit}`db.HasCatalog ?schema`, a hypothesis names the instance of the claim, while
a general hint such as {lit}`rfl` can choose an instance ({lit}`db` itself) that the next premises cannot
use. The kernel checks each proof at once ({name}`closesChecked`). The result is {lean}`false`, with no
change, when no attempt closes it. -/
def closeSide (hints : Hints) (goal : MVarId) : TacticM Bool := goal.withContext do
  if ← goal.isAssigned then return true
  let type ← instantiateMVars (← goal.getType)
  if ← closeByEvaluation goal then return true
  if ← closesWith goal (← `(tactic| assumption)) then return true
  for hint in hints do
    if ← closesWith goal (← `(tactic| exact $hint)) then return true
  if ← closesChecked goal (← `(tactic| exact rfl)) then return true
  if !type.hasFVar && !type.hasMVar then
    if ← closesWith goal (← `(tactic| decide +kernel)) then return true
  if !type.hasMVar then
    if ← closesChecked goal (← `(tactic| (simp [sql_select_simp]; done))) then return true
  return false

/-- Close the premises of an instantiated rule, except the one at {lit}`skip`, in order, and check that
each argument that is not a proposition is assigned. -/
def closePremises (hints : Hints) (arguments : Array Expr) (skip : Option Nat) : TacticM (Except Refusal Unit) := do
  for index in [0:arguments.size] do
    if skip == some index then continue
    let argument := arguments[index]!
    let goal := argument.mvarId!
    if ← goal.isAssigned then continue
    let type ← instantiateMVars (← inferType argument)
    if ← isProp type then
      unless ← closeSide hints goal do return .error (.premise type)
    else if (← isClass? type).isSome then
      let some solution ← (try some <$> synthInstance type catch _ => pure none) | return .error (.premise type)
      unless ← isDefEq argument solution do return .error (.premise type)
  for argument in arguments do
    if (← instantiateMVars argument).hasExprMVar && !(← isProp (← inferType argument)) then
      if !(← argument.mvarId!.isAssigned) then return .error (.premise (← inferType argument))
  return .ok ()

/-- Apply a rule backward: its conclusion must match the goal; its last explicit premise becomes the new
goal, and the procedure closes every other premise. The premises are the binders of the stated type of
the rule: a conclusion such as a check ({lit}`Sql.check`) is not unfolded into more premises. -/
def applyBackward (hints : Hints) (goal : MVarId) (rule : Expr) : TacticM (Except Refusal MVarId) :=
  goal.withContext do
    let saved ← Tactic.saveState
    let (arguments, binders, conclusion) ← forallMetaTelescope (← inferType rule)
    let some continuation := (← explicitPremises arguments binders).back? | return .error .noMatch
    unless ← isDefEq conclusion (← goal.getType) do
      saved.restore
      return .error .noMatch
    match ← closePremises hints arguments (some continuation) with
    | .error refusal =>
      saved.restore
      return .error refusal
    | .ok () =>
      goal.assign (mkAppN rule arguments)
      return .ok arguments[continuation]!.mvarId!

/-- Apply a rule forward to a hypothesis: the last explicit premise whose type matches the hypothesis
takes it, the procedure closes every other premise, and the conclusion becomes a new hypothesis. A
conclusion that a hypothesis already states is not added again. -/
def applyForward (hints : Hints) (goal : MVarId) (rule : Expr) (hypothesis : FVarId) :
    TacticM (Except Refusal MVarId) := goal.withContext do
  let saved ← Tactic.saveState
  let (arguments, binders, conclusion) ← forallMetaTelescope (← inferType rule)
  let hypothesisType ← hypothesis.getType
  let mut taken : Option Nat := none
  for index in (← explicitPremises arguments binders).reverse do
    if ← isDefEq (← inferType arguments[index]!) hypothesisType then
      arguments[index]!.mvarId!.assign (.fvar hypothesis)
      taken := some index
      break
  let some _ := taken | saved.restore; return .error .noMatch
  match ← closePremises hints arguments none with
  | .error refusal =>
    saved.restore
    return .error refusal
  | .ok () =>
    let fact ← instantiateMVars conclusion
    for declaration in ← getLCtx do
      if !declaration.isImplementationDetail && (← isDefEq declaration.type fact) then
        saved.restore
        return .error .noMatch
    let (_, next) ← (← goal.assert `fact fact (mkAppN rule arguments)).intro1P
    return .ok next

end Belay.Sqlite.Select
