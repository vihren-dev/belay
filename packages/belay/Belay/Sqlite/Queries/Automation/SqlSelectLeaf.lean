import Belay.Sqlite.Queries.Automation.SqlSelectSteps

set_option doc.verso true

/-! The last step of the procedure of {lit}`sql_select`: closing the goal that stays after the rules,
with the evaluation laws and the facts that the rules give. -/

namespace Belay.Sqlite.Select
open Lean Meta Elab Tactic

/-- Run a tactic on one goal. The result is the goals that the tactic leaves, or {lean}`none`, with no
change, when the tactic fails. The list of goals stays as it was. -/
def runsOn (goal : MVarId) (tactic : TSyntax `tactic) : TacticM (Option (List MVarId)) := do
  let saved ← Tactic.saveState
  try
    setGoals [goal]
    withoutRecover (Term.withoutErrToSorry (evalTactic tactic))
    let remaining ← getGoals
    setGoals saved.tactic.goals
    return some remaining
  catch _ =>
    saved.restore
    return none

/-- Unfold the definition at the head of the goal, for example a predicate of a row that the claim
names, until the head is not a definition of the user's modules. -/
def unfoldHead (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let some name := target.getAppFn.constName? | return goal
  let environment ← getEnv
  let some (.defnInfo _) := environment.find? name | return goal
  if (environment.getModuleIdxFor? name).any fun index =>
      let module := environment.header.moduleNames[index.toNat]!
      module.getRoot == `Init || module.getRoot == `Lean || module.getRoot == `Std then
    return goal
  let unfolded ← deltaExpand target (· == name)
  goal.replaceTargetDefEq unfolded

/-- The hints that the simplifier accepts as lemmas in the context of the goal. A hint such as {lit}`rfl`
or {lit}`⟨_, rfl⟩` closes premises, but it is no simp lemma, and the simplifier stops with an error on
the whole set when it gets one. The test elaborates {lit}`simp only [hint]` on a fresh goal
{lean}`True`, which the simplifier closes when it accepts the hint. -/
def simpLemmas (goal : MVarId) (hints : Hints) : TacticM (Array (TSyntax ``Parser.Tactic.simpLemma)) := do
  let mut accepted := #[]
  for hint in hints do
    let lemma ← `(Parser.Tactic.simpLemma| $hint:term)
    let probe ← goal.withContext do return (← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)).mvarId!
    if (← runsOn probe (← `(tactic| simp only [$lemma]))) == some [] then accepted := accepted.push lemma
  return accepted

/-- Close the last goal: unfold its head, then simplify the goal and the hypotheses with the evaluation
laws and the hints that are simp lemmas ({name}`simpLemmas`), then try {lit}`decide`, {lit}`omega` and
{lit}`assumption`. The last one closes a goal that a hypothesis gives up to the unfolding of definitions,
for example a named table shape of the claim against the evaluated shape that a rule gives. If the goal
stays open, a goal that is an
existential takes each hypothesis of the witness type as the witness, the most recent first, and a
conjunction is closed part by part, in the simplified context. The simplifier runs once for each goal,
because it is the most expensive step. The result is {lean}`false`, with no change, when the goal stays
open. -/
partial def finishLeaf (hints : Hints) (goal : MVarId) : TacticM Bool := do
  let saved ← Tactic.saveState
  let unfolded ← unfoldHead goal
  let lemmas ← simpLemmas unfolded hints
  let unfolded ← match ← runsOn unfolded (← `(tactic| simp_all [sql_select_simp, $lemmas,*])) with
    | some [] => return true
    | some [next] => pure next
    | _ => pure unfolded
  for attempt in #[← `(tactic| decide), ← `(tactic| omega), ← `(tactic| assumption)] do
    if ← closesWith unfolded attempt then return true
  let target ← unfolded.withContext do whnfR (← instantiateMVars (← unfolded.getType))
  if target.isAppOfArity ``Exists 2 then
    let witnessType := target.appFn!.appArg!
    let declarations ← unfolded.withContext do return (← getLCtx).decls.toArray.filterMap id
    for declaration in declarations.reverse do
      if declaration.isImplementationDetail then continue
      let fits ← unfolded.withContext do withNewMCtxDepth (isDefEq declaration.type witnessType)
      if !fits then continue
      let attempt ← Tactic.saveState
      let next ← unfolded.existsIntro (.fvar declaration.fvarId)
      if ← finishLeaf hints next then return true
      attempt.restore
  if target.isAppOfArity ``And 2 then
    let [left, right] ← unfolded.apply (mkConst ``And.intro) | saved.restore; return false
    if (← finishLeaf hints left) && (← finishLeaf hints right) then return true
  saved.restore
  return false

end Belay.Sqlite.Select
