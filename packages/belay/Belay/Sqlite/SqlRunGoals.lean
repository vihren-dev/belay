import Belay.Sqlite.SqlRunRules
import Belay.Sqlite.SqlRunTriples
import Belay.Sqlite.SendStepRules

set_option doc.verso true

/-! The goal operations of {lit}`sql_run` (ADR 0017, S6): closing a premise from the hints and hypotheses,
entering the goal of an outcome, bringing a triple to its check, and reporting where the tactic stopped.
Each operation changes the goal only by applying a theorem or by introducing variables, so the proof term
that the tactic builds is checked by the kernel. -/

namespace Belay.Sqlite.Run
open Lean Meta Elab Tactic Term

/-- The hints that the user passes: terms whose types close premises of the rules. -/
abbrev Hints := Array (TSyntax `term)

/-- The premises that hold by {lit}`rfl` once the program is known: the shape of a script. -/
def premisesByRfl : List Name := [`isStatement, `isSelect, `notInsertSelect]

/-- Try to close a premise about the context. The attempts are, in order, the hints, the hypotheses and
the facts that follow from a fresh start. A premise that no attempt closes stays open. -/
def closeSide (hints : Hints) (tag : Name) (goal : MVarId) : TacticM Bool := goal.withContext do
  let mut attempts : Array (TSyntax `tactic) := #[]
  if premisesByRfl.contains tag then attempts := attempts.push (← `(tactic| exact rfl))
  for hint in hints do
    attempts := attempts.push (← `(tactic| exact $hint))
    unless hint.raw.getKind == ``Lean.Parser.Term.anonymousCtor do
      attempts := attempts ++ #[← `(tactic| exact $hint _), ← `(tactic| exact $hint _ _), ← `(tactic| exact $hint _ _ _)]
  attempts := attempts.push (← `(tactic| assumption))
  attempts := attempts.push (← `(tactic| exact ExecutionContext.initial_holds_valid _ _))
  for attempt in attempts do
    try
      setGoals [goal]
      withoutRecover (Term.withoutErrToSorry (evalTactic attempt))
      if (← getGoals).isEmpty then return true
    catch _ => pure ()
  return false

/-- Introduce the variables and hypotheses of an outcome premise under the given names, and replace the
variable {lit}`next` by the connection that the equation {lit}`nextIs` gives. -/
def enterOutcome (names : List Name) (replacesNext : Bool) (goal : MVarId) : TacticM MVarId := do
  let (fvars, goal) ← goal.introN names.length names
  unless replacesNext do return goal
  goal.withContext do
    for fvar in fvars do
      let type ← instantiateMVars (← fvar.getType)
      if let some (_, .fvar local_, _) := type.eq? then
        if (← local_.getUserName) == `next then
          let (_, goal) ← substCore goal fvar (symm := false) (tryToSkip := true)
          return goal
    throwError "sql_run: the rule gave no equation for the next connection"

/-- Close the goal of a failed step when its trace is not error-free: the final property of a conditional
claim ({name}`Sql.ifOk`) then requires nothing. -/
def closeFailure (goal : MVarId) : TacticM (List MVarId) := goal.withContext do
  setGoals [goal]
  try
    evalTactic (← `(tactic| (intro allOk; simp [List.allOk, ExecutionContext.next, *] at allOk)))
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

end Belay.Sqlite.Run
