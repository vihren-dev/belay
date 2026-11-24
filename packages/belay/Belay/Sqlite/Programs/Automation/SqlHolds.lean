import Belay.Sqlite.Programs.Automation.SqlHoldsRuns
import Belay.Sqlite.Frontend.Embedding.SqlTerm

set_option doc.verso true

/-! The tactic {lit}`sql_holds [hints]` proves the goal that {lit}`sql_run` leaves for a claim {lit}`holds q` or
{lit}`holdsSince start q` down to goals about rows of tables. A hint is a proof of {lit}`db.HasCatalog schema` for
each database that the claim reads. The tactic applies these laws, in order:

* for {lit}`holdsSince start q` with a {lit}`SELECT` that names no schema, the law to the one-state claim
  ({name}`Belay.Sqlite.Holds.reachedSince_iff_reached`), so that the claim needs no catalog of {lit}`start`;
* the bridge from the claim to the output of the resolved query, with the resolution that the kernel computes on
  the catalog of the hint ({name}`Belay.Sqlite.Holds.reached_iff_of_catalog`,
  {name}`Belay.Sqlite.Holds.reachedSince_iff_of_catalog`);
* the law of {lit}`SELECT 1 WHERE c` ({name}`Belay.Sqlite.Model.resolvedStepOutput_selectOneWhere_hasRows`),
  with the calm premise that the kernel decides;
* the law of {lit}`EXISTS` or {lit}`NOT EXISTS` of a subquery
  ({name}`Belay.Sqlite.Model.Resolved.Expr.truthy_exists`, {name}`Belay.Sqlite.Model.Resolved.Expr.truthy_notExists`);
* the laws of the subqueries: the read of one table and {lit}`EXCEPT`.

The goals that stay open name rows of tables, {lit}`Resolved.Expr.eval` with the bound values, {lit}`truthy`, and
the data functions of the statements that ran. When no law fits a part of the query, the tactic fails with a
message that names that part. -/

namespace Belay.Sqlite.ClaimTactic
open Lean Meta Elab Tactic Model

/-- Rewrite the target of a goal with an equation. -/
def rewriteGoal (goal : MVarId) (equation : Expr) : MetaM MVarId := do
  let result ← goal.rewrite (← goal.getType) equation
  goal.replaceTargetEq result.eNew result.eqProof

/-- Apply an equivalence law to a goal and return the goal for its right side. -/
def applyEquivalence (hints : Array Expr) (law : Name) (goal : MVarId) : MetaM (MVarId × Array Expr) := do
  let (equivalence, right, open_) ← applyLaw hints law (← instantiateMVars (← goal.getType))
  let next ← mkFreshExprSyntheticOpaqueMVar right (← goal.getTag)
  goal.assign (← mkAppM ``Iff.mpr #[equivalence, next])
  return (next.mvarId!, open_)

/-- Bring a two-state claim whose query names no schema to the one-state claim
({name}`Belay.Sqlite.Holds.reachedSince_iff_reached`), so that it needs no catalog of the initial database. The
result is {lean}`(none : Option MVarId)` when the kernel does not decide that the query is a {lit}`SELECT` that names
no schema. -/
def oneStateClaim? (goal : MVarId) : MetaM (Option MVarId) := do
  let saved ← saveState
  let (next, open_) ← applyEquivalence #[] ``Holds.reachedSince_iff_reached goal
  for premise in open_ do
    let some proof ← Select.evaluationProof? (← instantiateMVars (← inferType premise)) | saved.restore; return none
    premise.mvarId!.assign proof
  return some next

/-- Bring the claim to the output of its resolved query. -/
def bridge (hints : Array Expr) (goal : MVarId) : MetaM MVarId := do
  let (law, goal) ← match_expr ← instantiateMVars (← goal.getType) with
    | Holds.reached _ _ _ => pure (``Holds.reached_iff_of_catalog, goal)
    | Holds.reachedSince _ _ _ _ => match ← oneStateClaim? goal with
      | some next => pure (``Holds.reached_iff_of_catalog, next)
      | none => pure (``Holds.reachedSince_iff_of_catalog, goal)
    | _ => throwError "sql_holds proves the goal that sql_run leaves for a claim holds q or holdsSince start q. \
        Use it after sql_run, on the goal of the claim."
  let (next, open_) ← applyEquivalence hints law goal
  unless open_.isEmpty do
    throwError m!"sql_holds cannot resolve the query of the claim on the catalog of the hint. Check that the \
      hint gives the catalog of each database that the claim reads.{indentD (← open_.mapM inferType)}"
  return next

/-- The words for the first clock expression of a statement without variables that fails
{name}`Belay.Sqlite.Model.Resolved.Expr.calmCheck`: it reads the clock or a counter, or calls a function that can
fail. When the kernel shows no such expression, the words say that the kernel does not decide the check. -/
def restlessPart (statement : Expr) : MetaM MessageData := do
  let expressions ← Select.kernelNormalize (← mkAppM ``Resolved.Statement.clockExpressions #[statement])
  for expression in (← listElements? expressions).getD [] do
    let check ← mkAppM ``Resolved.Expr.calmCheck #[expression]
    if let .ok value := Kernel.whnf (← getEnv) (← getLCtx) check then
      if value.isConstOf ``Bool.false then
        return m!"the expression{indentExpr expression}\nwhich reads the clock or a counter, or calls a function \
          that can fail"
  return "a claim for which the kernel does not decide that it reads no clock and no counter and calls no function \
    that can fail"

/-- Bring the output of {lit}`SELECT 1 WHERE c` to the truth of {lit}`c`. The result is the goal, the premise that
{lit}`c` has no fault, and {lit}`c`. -/
def selectOneWhere (hints : Array Expr) (goal : MVarId) : MetaM (MVarId × Expr × Expr) := do
  let_expr Eq _ hasRows _ := ← instantiateMVars (← goal.getType) | noLaw "the output of the claim"
  let_expr Output.hasRows step := hasRows | noLaw "the output of the claim"
  let_expr resolvedStepOutput _ _ _ _ resolved _ := step | noLaw m!"the output{indentExpr step}"
  let_expr Resolved.Statement.query query subqueries := ← whnfD resolved | noLaw "a claim that is not a SELECT"
  let_expr Option.some _ condition := ← queryField query `filter | noLaw m!"a claim without WHERE{indentExpr query}"
  let expected ← mkAppM ``Resolved.Query.selectOneWhere #[condition]
  unless ← isDefEq query expected do noLaw (← differingPart query expected)
  let (next, open_) ← applyEquivalence hints ``resolvedStepOutput_selectOneWhere_hasRows goal
  let #[calm, quiet] := open_ | throwError "sql_holds: unexpected premises of the law of SELECT 1 WHERE"
  let statement ← mkAppM ``Resolved.Statement.query #[expected, subqueries]
  let some calmProof ← decidedLaw? ``Resolved.Statement.calm_of_calmCheck statement | noLaw (← restlessPart statement)
  calm.mvarId!.assign calmProof
  return (next, quiet, condition)

/-- Bring the truth of {lit}`EXISTS` or {lit}`NOT EXISTS` of a subquery to the rows of the subquery, and close the
premise that the condition has no fault. The result is the goals that stay open. -/
def existsCondition (hints : Array Expr) (goal : MVarId) (quiet condition : Expr) : MetaM (Array MVarId) := do
  let (index, negated) ← match_expr condition with
    | Resolved.Expr.not inner => do
      let_expr Resolved.Expr.exists index := inner | noLaw m!"the condition{indentExpr condition}"
      pure (index, true)
    | Resolved.Expr.exists index => pure (index, false)
    | _ => noLaw m!"the condition{indentExpr condition}\nwhich is not EXISTS or NOT EXISTS of a subquery"
  let_expr Eq _ truth _ := ← goal.getType | noLaw "the truth of the condition"
  let_expr Resolved.truthy value := truth | noLaw "the truth of the condition"
  let_expr Resolved.Expr.eval context row _ := value | noLaw "the truth of the condition"
  let truthLaw := if negated then ``Resolved.Expr.truthy_notExists else ``Resolved.Expr.truthy_exists
  let goal ← rewriteGoal goal (← mkAppM truthLaw #[context, row, index])
  let fact ← subqueryFact hints (← mkAppM ``Resolved.EvalContext.subqueries #[context, index, row])
  let mut fault ← mkEqTrans (← mkAppM ``Resolved.Expr.fault_exists #[context, row, index]) fact.fault
  if negated then
    let operand ← mkAppM ``Resolved.Expr.exists #[index]
    fault ← mkEqTrans (← mkAppM ``Resolved.Expr.fault_not #[context, row, operand]) fault
  quiet.mvarId!.assign fault
  return #[← rewriteGoal goal fact.rows] ++ fact.goals

/-- {lit}`sql_holds [h₁, …]` proves the goal that {lit}`sql_run` leaves for a claim {lit}`holds q` or
{lit}`holdsSince start q` down to goals about rows of tables. Each hint is a proof of {lit}`db.HasCatalog schema`
for a database that the claim reads. For example, after {lit}`sql_run` in a proof of a claim
{lean}`fun x : Value => holds (sql r"SELECT 1 WHERE NOT EXISTS (SELECT * FROM t WHERE c = $x)")` about each
database with the catalog of {lit}`schema`, {lit}`sql_holds [catalog]` leaves the goal that each row of {lit}`t`
does not satisfy the condition. -/
syntax (name := sqlHolds) "sql_holds" (" [" term,* "]")? : tactic

/-- The elaborator of {lit}`sql_holds`: it introduces the premises, unfolds {lit}`holds` and {lit}`holdsSince`,
applies the laws in order and simplifies each goal that stays open. -/
@[tactic sqlHolds] def evalSqlHolds : Tactic := fun syntax_ => do
  let hintTerms := match syntax_ with
    | `(tactic| sql_holds [$hints,*]) => hints.getElems
    | _ => #[]
  let siblings := (← getUnsolvedGoals).drop 1
  let (_, goal) ← (← getMainGoal).intros
  setGoals [goal]
  evalTactic (← `(tactic| try simp only [Belay.Sqlite.holds, Belay.Sqlite.holdsSince, Std.Do.SPred.down_pure_nil]))
  let goal ← getMainGoal
  let goals ← goal.withContext do
    let hints ← hintTerms.mapM fun hint => do instantiateMVars (← Tactic.elabTerm hint none)
    let (truth, quiet, condition) ← selectOneWhere hints (← bridge hints goal)
    existsCondition hints truth quiet condition
  let mut remaining := #[]
  for open_ in goals do
    setGoals [open_]
    evalTactic (← `(tactic| try simp only [List.isEmpty_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff,
      Option.all_some, Option.all_none, Bool.not_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem]))
    evalTactic (← `(tactic| try dsimp only [Belay.Sqlite.Database.Raw.connection, Belay.Sqlite.ExecutionContext.next,
      Belay.Sqlite.ExecutionContext.initial, Belay.Sqlite.Model.Connection.afterWrite]))
    remaining := remaining ++ (← getGoals)
  setGoals (remaining.toList ++ siblings)

end Belay.Sqlite.ClaimTactic
