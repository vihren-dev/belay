import Belay.Sqlite.SqlRunGoals
import Belay.Sqlite.ExecutionSpecifications

set_option doc.verso true

/-! The tactic {lit}`sql_run` (ADR 0017, S6). It reduces the check of a SQL program to the obligations
that the public step rules leave: for each sent statement the resolution, the table, the model's
coverage, and the goals for the success and the failure of the step, then the check of the rest of the
program at the reached connection. Every rule is a theorem; the tactic only applies them, so a proof it
builds is checked by the kernel like any other proof. -/

namespace Belay.Sqlite.Run
open Lean Meta Elab Tactic Term

/-- The goals of the program after one rule, each processed by its role. -/
partial def runGoal (hints : Hints) (first : Bool) (fuel : Nat) (goal : MVarId) : TacticM (List MVarId) :=
  withFreshMacroScope <| goal.withContext do
  if fuel == 0 then return ← stuck first goal "the program unfolds without end."
  let goal ← enterCheck goal
  let some program ← checkProgram? (← goal.getType)
    | if first then
        throwError "sql_run proves a check of a SQL program, a triple, or the goal that mvcgen leaves for one. This goal is none of these. Use another tactic, or state the claim with Sql.check."
      else return [goal]
  let apply (tactic : TSyntax `tactic) : TacticM (List MVarId) := do
    setGoals [goal]
    evalTactic tactic
    let goals ← getGoals
    let mut open_ := []
    for new in goals do
      open_ := open_ ++ (← runGoal hints false (fuel - 1) new)
    return open_
  match ← classifyProgram program with
  | .bind => apply (← `(tactic| refine (Sql.check_bind _ _ _ _).2 ?_))
  | .pure => apply (← `(tactic| refine (Sql.check_pure _ _ _).2 ?_))
  | .map => apply (← `(tactic| refine (Sql.check_map _ _ _ _).2 ?_))
  | .branch => apply (← `(tactic| split))
  | .single script => runRead hints first fuel goal script true
  | .query script => runRead hints first fuel goal script false
  | .send script => runSend hints first fuel goal script
  | .raw => stuck first goal "the program is a raw execution step."
  | .opaque => stuck first goal "the program is a variable or an unknown term."
  | .definition _ =>
    match ← unfoldDefinition? program with
    | none => stuck first goal "the program is a definition that does not unfold."
    | some unfolded =>
      let target ← whnfR (← goal.getType)
      let goal ← goal.replaceTargetDefEq (mkAppN target.getAppFn (target.getAppArgs.set! 1 unfolded))
      runGoal hints first (fuel - 1) goal
where
  /-- Apply the rule of a read to a goal whose program is a single or a query of one SELECT statement. The
  goals of the rule are the model coverage and the post for every selected output. -/
  runRead (hints : Hints) (first : Bool) (fuel : Nat) (goal : MVarId) (script : Expr) (single : Bool) : TacticM (List MVarId) := do
    let some (statement, values, rest) ← firstStatement? script
      | stuck first goal "the script is not a list of statements that Lean can read."
    unless ← isLast rest do return ← stuck first goal "a query reads one statement, and the script has more."
    unless (← statementKind? statement) == some ``Model.Syntax.Statement.select do
      return ← stuck first goal "only a SELECT statement has a rule for its rows."
    let (statement, values) := (← exprToSyntax statement, ← exprToSyntax values)
    setGoals [goal]
    if single then
      evalTactic (← `(tactic| refine Sql.check_single_select (statement := $statement) (values := $values) rfl rfl ?modeled ?reached))
    else
      evalTactic (← `(tactic| refine Sql.check_query_select (statement := $statement) (values := $values) rfl rfl ?modeled ?reached))
    processPremises hints fuel ``Model.Syntax.Statement.select (← getGoals)
  /-- Apply the rule of a sent script to a goal. A script of several statements is split after its first
  statement, so that each statement gets its own rule at the context that the earlier ones reach. -/
  runSend (hints : Hints) (first : Bool) (fuel : Nat) (goal : MVarId) (script : Expr) : TacticM (List MVarId) := do
    let some (statement, values, rest) ← firstStatement? script
      | stuck first goal "the script is not a list of statements that Lean can read."
    if !(← isLast rest) then
      let pair ← mkAppM ``Prod.mk #[statement, values]
      let first ← mkAppM ``Script.mk #[← mkListLit (← inferType pair) [pair]]
      let second ← mkAppM ``Script.mk #[rest]
      setGoals [goal]
      evalTactic (← `(tactic| refine (check_send_append $(← exprToSyntax first) $(← exprToSyntax second) _ _).2 ?_))
      let mut open_ := []
      for new in ← getGoals do open_ := open_ ++ (← runGoal hints false (fuel - 1) new)
      return open_
    let some kind ← (do match ← statementKind? statement with
        | some kind => pure (some kind)
        | none => kindFromHints hints goal)
      | stuck first goal "the statement is not a constructor that Lean can read, and no hint closes the resolution of an insert, update, delete or ADD COLUMN."
    setGoals [goal]
    evalTactic (← sendRule kind)
    processPremises hints fuel kind (← getGoals)
  /-- Process the premises that a rule leaves. A premise about the context is closed from the hints or stays
  open. An outcome premise is entered, and the rest of the program runs inside it. The outcome premises stay
  open when a premise that they depend on is open. -/
  processPremises (hints : Hints) (fuel : Nat) (kind : Name) (goals : List MVarId) : TacticM (List MVarId) := do
    let mut open_ := []
    let mut blocked := false
    let premises ← goals.filterM fun new => return premiseNames.contains (← new.getTag).eraseMacroScopes
    let variables := goals.filter fun new => !premises.contains new
    for new in premises do
      let tag := (← new.getTag).eraseMacroScopes
      match roleOf kind tag with
      | .side =>
        unless ← closeSide hints tag new do
          open_ := open_ ++ [new]
          blocked := blocked || blockingPremises.contains tag
      | .outcome names replacesNext =>
        if blocked then
          open_ := open_ ++ [new]
        else
          let entered ← enterOutcome names replacesNext new
          let rest ← runGoal hints false (fuel - 1) entered
          if tag == `failure then
            for goal in rest do open_ := open_ ++ (← closeFailure goal)
          else open_ := open_ ++ rest
    return (← variables.filterM fun data => return !(← data.isAssigned)) ++ open_

/-- Apply the step rules to the check of a SQL program, and leave the obligations that the rules do not
discharge. The optional terms are hints: each is tried against each premise about the context, for
example the resolution of a statement. -/
syntax (name := sqlRun) "sql_run" (" [" term,* "]")? : tactic

/-- Run {lit}`sql_run`: process the main goal and put the open obligations in place of it. -/
@[tactic sqlRun] def evalSqlRun : Tactic := fun stx => do
  let hints : Hints := match stx with
    | `(tactic| sql_run [$hints,*]) => hints.getElems
    | _ => #[]
  let goal ← getMainGoal
  let siblings := (← getGoals).drop 1
  let remaining ← runGoal hints true traversalFuel goal
  let tidied ← remaining.mapM tidy
  setGoals (tidied ++ siblings)

end Belay.Sqlite.Run
