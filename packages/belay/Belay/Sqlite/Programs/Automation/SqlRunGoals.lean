import Belay.Sqlite.Programs.Automation.SqlRunRules
import Belay.Sqlite.Programs.Reasoning.SqlRunTriples

set_option doc.verso true

/-! The goal operations of {lit}`sql_run` (ADR 0017, S6): closing a premise from the hints and hypotheses,
bringing a triple to its check, and reporting where the tactic stopped.
Each operation changes the goal only by applying a theorem or by introducing variables, so the proof term
that the tactic builds is checked by the kernel. -/

namespace Belay.Sqlite.Run
open Lean Meta Elab Tactic Term

/-- The hints that the user passes: terms whose types close premises of the rules. -/
abbrev Hints := Array (TSyntax `term)

/-- The premises that hold by {lit}`rfl` once the program is known: the shape of a script. -/
def premisesByRfl : List Name := [`isSelect, `notInsertSelect]

/-- Try to close a premise about the context. The attempts are, in order, the hints, each also with all definitions
unfolded (a resolution of CREATE TABLE needs it), the hypotheses and the facts that follow from a fresh start. A premise that no attempt closes stays open. -/
def closeSide (hints : Hints) (tag : Name) (goal : MVarId) : TacticM Bool := goal.withContext do
  let mut attempts : Array (TSyntax `tactic) := #[]
  if premisesByRfl.contains tag then
    attempts := attempts ++ #[← `(tactic| exact rfl), ← `(tactic| with_unfolding_all exact rfl)]
  for hint in hints do
    attempts := attempts ++ #[← `(tactic| exact $hint), ← `(tactic| with_unfolding_all exact $hint)]
    unless hint.raw.getKind == ``Lean.Parser.Term.anonymousCtor do
      attempts := attempts ++ #[← `(tactic| exact $hint _), ← `(tactic| exact $hint _ _), ← `(tactic| exact $hint _ _ _),
        ← `(tactic| exact $hint _ rfl), ← `(tactic| exact $hint _ _ rfl)]
  attempts := attempts.push (← `(tactic| assumption))
  attempts := attempts.push (← `(tactic| exact ExecutionContext.initial_holds_valid _ _))
  for attempt in attempts do
    try
      setGoals [goal]
      withoutRecover (Term.withoutErrToSorry (evalTactic attempt))
      if (← getGoals).isEmpty then return true
    catch _ => pure ()
  return false

/-- Close the goal of a failed step when its trace is not error-free: the final property of a conditional
claim ({name}`Sql.ifOk`) then requires nothing. The error is a hypothesis of the step rule, or the output
{lit}`.error` that a kind rule gives. -/
def closeFailure (goal : MVarId) : TacticM (List MVarId) := goal.withContext do
  setGoals [goal]
  try
    evalTactic (← `(tactic| first
      | (intro allOk; simp [List.allOk, ExecutionContext.next, *] at allOk; done)
      | (intro allOk; simp [List.allOk, ExecutionContext.next, Model.Output.isError] at allOk; done)
      | (intro allOk; simp [List.allOk, ExecutionContext.next, *] at allOk)))
    return (← getGoals)
  catch _ => return [goal]

/-- Show an open goal in the form of the claim: remove the postcondition wrapper and the application of the
claim to the start. -/
def tidy (goal : MVarId) : TacticM MVarId := goal.withContext do
  setGoals [goal]
  try
    evalTactic (← `(tactic| (try dsimp only [Std.Do.PostCond.noThrow]); (try simp only [Std.Do.SPred.down_pure_nil])))
  catch _ => pure ()
  return (← getGoals).headD goal

/-- Report the place where the tactic stopped. Before the first rule, the whole tactic fails with the reason, so
that an alternative such as {lit}`first` can try another tactic from the unchanged goal. After a rule, the
goal stays as an obligation and the reason is a warning. -/
def stuck (first : Bool) (goal : MVarId) (reason : String) : TacticM (List MVarId) := do
  if first then
    throwError "sql_run cannot start: {reason} Prove this goal with the public rules, for example Sql.check_bind and Sql.check_send_of_step."
  logWarning m!"sql_run stopped: {reason} The goal stays open."
  return [goal]

/-- Bring a goal that is a standard triple, or a verification condition of one, to the check of the program.
A triple becomes a check from every context that meets its precondition; a condition that mvcgen leaves,
{lit}`∀ state, pre → (wp⟦program⟧ post state).down`, becomes the check at the introduced state. An equation
{lit}`state = context` among the introduced hypotheses, or among the hypotheses of a goal that is already a
check, is used to replace the state. Other goals stay. -/
def enterCheck (goal : MVarId) : TacticM MVarId := goal.withContext do
  let type ← whnfR (← instantiateMVars (← goal.getType))
  if type.isAppOf ``Std.Do.Triple then
    setGoals [goal]
    evalTactic (← `(tactic| refine Sql.triple_iff_check.2 ?_))
    let goal ← getMainGoal
    let (fvars, goal) ← goal.intros
    return ← substEquations goal fvars
  let isWp (body : Expr) : Bool := body.isAppOf ``ULift.down && body.getAppArgs.back!.isAppOf ``Std.Do.WP.wp
  let isCondition ← forallTelescope type fun binders body => pure (!binders.isEmpty && isWp body)
  if isCondition then
    let (fvars, goal) ← goal.intros
    return ← substEquations goal fvars
  if isWp type then
    setGoals [goal]
    evalTactic (← `(tactic| refine (Sql.wp_down_iff_check _ _ _).2 ?_))
    return ← getMainGoal
  substLocalEquations goal
where
  /-- Replace a state variable of the goal by the context that an equation of the local context gives, as in the
  goal that mvcgen leaves for the program of a triple. -/
  substLocalEquations (goal : MVarId) : TacticM MVarId := goal.withContext do
    let mut goal := goal
    for local_ in (← getLCtx) do
      if local_.isImplementationDetail then continue
      if let some (_, .fvar stateVar, _) := (← instantiateMVars local_.type).eq? then
        if (← goal.getType).containsFVar stateVar then
          try goal := (← substCore goal local_.fvarId (symm := false) (tryToSkip := true)).2 catch _ => pure ()
    return goal
  /-- Replace each introduced variable that an introduced equation defines, so that the hints speak about the
  initial context and not about a name for it. -/
  substEquations (goal : MVarId) (fvars : Array FVarId) : TacticM MVarId := goal.withContext do
    let mut goal := goal
    for fvar in fvars do
      let type ← instantiateMVars (← fvar.getType)
      if let some (_, .fvar _, _) := type.eq? then
        try goal := (← substCore goal fvar (symm := false) (tryToSkip := true)).2 catch _ => pure ()
    return goal

/-- Ask the hints for the resolution of this step with the resolved statement and
post-resolution state left as variables. A proof lets rule selection compare the
resolved data without elaborating all the hints again for each candidate. If a hint
needs the expected kind to elaborate, selection still tries it on the individual rules. -/
def hintedResolution (hints : Hints) (equation : MVarId) : TacticM (Option Expr) := equation.withContext do
  let saved ← Tactic.saveState
  try
    let some (_, step, _) := (← whnfR (← equation.getType)).eq? | return none
    let #[context, _, _, connection, statement, _] := step.getAppArgs | return none
    unless step.isAppOf ``Model.runScriptStep do return none
    let lhs ← mkAppM ``Model.resolveStatement #[context, ← mkAppM ``Model.Connection.resolveState #[connection], statement]
    let resolved ← mkFreshExprMVar (mkConst ``Model.Resolved.Statement)
    let after ← mkFreshExprMVar (mkConst ``Model.ResolveState)
    let pair ← mkAppM ``Prod.mk #[resolved, after]
    let result ← whnf (← inferType lhs)
    let rhs ← mkAppOptM ``Except.ok #[some result.getAppArgs[0]!, none, some pair]
    let proof ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs rhs)
    if ← closeSide hints `found proof.mvarId! then
      let proof ← instantiateMVars proof
      unless proof.hasExprMVar do return some proof
  catch _ => pure ()
  saved.restore
  return none

end Belay.Sqlite.Run
