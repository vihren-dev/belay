import Belay.Sqlite.SqlSelectRule
import Belay.Sqlite.SqlSelectEval
import Lean.Elab.Tactic
import Lean.Meta.Closure

set_option doc.verso true

/-! The steps of the procedure of {lit}`sql_select`: closing a premise of a rule, applying a rule to the
goal (backward) and applying a rule to a hypothesis (forward). Each step changes the goal only by an
application of a proved theorem, so the kernel checks the proof that the procedure builds. A step that
fails leaves the goal and the metavariables as they were. -/

namespace Belay.Sqlite.Select
open Lean Meta Elab Tactic

/-- The hints that the user passes: rules and facts, for example a catalog premise {lit}`schema`. -/
abbrev Hints := Array (TSyntax `term)

/-- Run a tactic on one goal. The result is {lean}`true` when the tactic closes the goal; otherwise the
state is restored and the result is {lean}`false`. The list of goals stays as it was. -/
def closesWith (goal : MVarId) (tactic : TSyntax `tactic) : TacticM Bool := do
  let saved ← Tactic.saveState
  try
    setGoals [goal]
    withoutRecover (Term.withoutErrToSorry (evalTactic tactic))
    if (← getGoals).isEmpty then
      setGoals saved.tactic.goals
      return true
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

/-- Close a goal with a tactic, and check the proof with the kernel at once, as an auxiliary theorem
that takes the place of the proof. The result is {lean}`false`, with no change, when the tactic fails
or the kernel refuses the proof, for example because its recursion is too deep. A proof that the kernel
cannot check would otherwise fail the whole theorem at its end. A goal whose type has metavariables
keeps the tactic's proof unchecked: the tactic can assign metavariables that other goals share, such as
the statement of a script with a parameter, and a restored state would lose them. -/
def closesChecked (goal : MVarId) (tactic : TSyntax `tactic) : TacticM Bool := do
  let saved ← Tactic.saveState
  let sharesMetavariables := (← instantiateMVars (← goal.getType)).hasMVar
  unless ← closesWith goal tactic do return false
  let type ← instantiateMVars (← goal.getType)
  let proof ← instantiateMVars (.mvar goal)
  if sharesMetavariables || proof.hasMVar then return true
  saved.restore
  try
    let checked ← goal.withContext (mkAuxTheorem type proof (zetaDelta := true))
    goal.assign checked
    return true
  catch _ =>
    saved.restore
    return false

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

/-- The term of a rule: a global theorem with fresh universe levels, or an elaborated hint. The result is
{lean}`none`, with no change and no message, for a hint that has no type of its own, such as the
anonymous constructor {lit}`⟨_, rfl⟩`: such a hint only closes premises and goals, whose types it takes. -/
def ruleTerm (rule : Sum Name (TSyntax `term)) : TermElabM (Option Expr) :=
  match rule with
  | .inl name => some <$> mkConstWithFreshMVarLevels name
  | .inr hint => do
    if hint.raw.isIdent then
      if let some name ← (try some <$> realizeGlobalConstNoOverload hint.raw catch _ => pure none) then
        return some (← mkConstWithFreshMVarLevels name)
    -- The elaborator logs some errors, such as a stuck anonymous constructor, and does not throw them.
    let messages ← Core.getMessageLog
    Core.resetMessageLog
    let saved ← saveState
    let term ← try
        Term.withoutErrToSorry do
          let term ← Term.elabTerm hint none
          Term.synthesizeSyntheticMVarsNoPostponing
          pure (some (← instantiateMVars term))
      catch _ => pure none
    let term := if (← Core.getMessageLog).hasErrors then none else term
    if term.isNone then saved.restore
    modifyThe Core.State fun state => { state with messages := messages ++ state.messages }
    return term

/-- Why a rule did not apply: its conclusion or trigger does not match, or one of its premises stays
open, with the type of the premise. -/
inductive Refusal where
  /-- The rule does not match the goal or the hypothesis. -/
  | noMatch
  /-- A premise of the rule stays open. -/
  | premise (type : Expr)

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

/-- The indexes of the explicit premises of a rule that are propositions. -/
def explicitPremises (arguments : Array Expr) (binders : Array BinderInfo) : MetaM (Array Nat) := do
  let mut found := #[]
  for index in [0:arguments.size] do
    if binders[index]!.isExplicit && (← isProp (← inferType arguments[index]!)) then found := found.push index
  return found

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
