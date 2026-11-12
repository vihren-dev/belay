import Belay.Sqlite.Queries.Automation.SqlSelectRule
import Lean.Elab.Tactic
import Lean.Meta.Closure

set_option doc.verso true

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

/-- The indexes of the explicit premises of a rule that are propositions. -/
def explicitPremises (arguments : Array Expr) (binders : Array BinderInfo) : MetaM (Array Nat) := do
  let mut found := #[]
  for index in [0:arguments.size] do
    if binders[index]!.isExplicit && (← isProp (← inferType arguments[index]!)) then found := found.push index
  return found

end Belay.Sqlite.Select
