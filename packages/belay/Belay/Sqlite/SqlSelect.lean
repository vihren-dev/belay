import Belay.Sqlite.SqlSelectLeaf
import Belay.Sqlite.SqlSelectRules
import Belay.Sqlite.SelectCatalogExecution
import Lean.Meta.Tactic.Subst

set_option doc.verso true

/-! The tactic {lit}`sql_select` (ADR 0027, D6): it proves a claim about the results of a SELECT by
proved phase rules. The procedure introduces the binders of the goal, applies an execution rule backward,
which turns a claim about a run, or the check of a query ({lit}`Sql.check`), into a claim about every
result that the model permits for the query,
then applies the rules of the other phases forward to the hypotheses that it introduces, splits the
facts that they give, and closes the last goal with the evaluation laws. The explicit hints run first,
in the given order, then the registered rules of the phase ({lit}`sql_select_rule`), in qualified
declaration-name order. A goal that the procedure cannot close stays open, with an explanation. -/

namespace Belay.Sqlite.Select
open Lean Meta Elab Tactic

/-- For every list of length {lit}`n + 1`, the list is a first element and a rest of length {lit}`n`. -/
theorem cons_of_length_succ {α : Type} {list : List α} {n : Nat} (length : list.length = n + 1) :
    ∃ head tail, list = head :: tail ∧ tail.length = n := by
  cases list with
  | nil => simp at length
  | cons head tail => exact ⟨head, tail, rfl, by simpa using length⟩

/-- The phases whose rules apply to a hypothesis of the given type: membership in the results of a
query, membership in the scanned rows of a table, or any other fact. -/
def phasesOfFact (type : Expr) : List SelectPhase :=
  match type.getAppFnArgs with
  | (``Membership.mem, #[_, _, _, collection, _]) =>
    match collection.getAppFn.constName? with
    | some ``Belay.Sqlite.Model.Resolved.Query.possibleResults =>
      [.window, .order, .distinct, .project, .having, .aggregate, .group, .compound, .subquery]
    | some ``Belay.Sqlite.Database.scanAt => [.source]
    | _ => [.filter, .expression]
  | _ => [.filter, .expression]

/-- The rules to try on a goal or a fact of the phases: the hints in the given order, then the
registered rules. -/
def candidates (hints : Hints) (phases : List SelectPhase) : TacticM (Array (Sum Name (TSyntax `term))) := do
  return hints.map .inr ++ (← registeredSelectRules phases).map (.inl ·.2)

/-- Split a hypothesis that is an existential or a conjunction into its parts, and a hypothesis that a
list variable has a fixed length into its elements, until none is left; then substitute each variable
that a hypothesis equates to a term. The length can be any closed term, which the kernel computes. -/
partial def splitFacts (goal : MVarId) : MetaM MVarId := goal.withContext do
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let type ← whnfR (← instantiateMVars declaration.type)
    if type.isAppOf ``Exists || type.isAppOf ``And then
      let #[split] ← goal.cases declaration.fvarId | return goal
      return ← splitFacts split.mvarId
    if let some (_, left, right) := type.eq? then
      if left.isAppOfArity ``List.length 2 && left.appArg!.isFVar then
        let some length ← evaluateNatural? right | continue
        if length == 0 then continue
        let stated ← mkEq left (mkNatLit length)
        let proof ← mkExpectedTypeHint (.fvar declaration.fvarId) stated
        let proof ← mkAppM ``cons_of_length_succ #[proof]
        let next ← goal.assert `cells (← inferType proof) proof
        let next ← next.clear declaration.fvarId
        let (_, next) ← next.intro1P
        return ← splitFacts next
  substVars goal

/-- The key of a rule in the record of applied steps: its name, or the text of a hint. -/
def ruleKey : Sum Name (TSyntax `term) → String
  | .inl name => toString name
  | .inr hint => toString hint.raw.prettyPrint

/-- Apply forward rules to the hypotheses until no rule gives a new fact or the fuel ends, splitting the
facts after each step. Each rule applies at most once to a fact, so that a rule whose fact has a new
witness does not repeat; for a membership the fact is the collection, which a substitution of the
member does not change. -/
partial def saturate (hints : Hints) (fuel : Nat) (applied : Std.HashSet (String × Expr)) (goal : MVarId) :
    TacticM MVarId := do
  if fuel == 0 then return goal
  let goal ← splitFacts goal
  let hypotheses ← goal.withContext do
    return (← getLCtx).foldl (init := #[]) fun found declaration =>
      if declaration.isImplementationDetail then found else found.push declaration
  for hypothesis in hypotheses do
    let type ← instantiateMVars hypothesis.type
    let rules ← goal.withContext do candidates hints (phasesOfFact type)
    let fact := match type.getAppFnArgs with
      | (``Membership.mem, #[_, _, _, collection, _]) => collection
      | _ => type
    for rule in rules do
      let key := (ruleKey rule, fact)
      if applied.contains key then continue
      let term ← goal.withContext (ruleTerm rule)
      if let .ok next ← applyForward hints goal term hypothesis.fvarId then
        return ← saturate hints (fuel - 1) (applied.insert key) next
  return goal

/-- Report where the procedure stopped and why; the goal stays open. -/
def explain (goal : MVarId) (phase : String) (reason : MessageData) : TacticM Unit :=
  logWarning m!"sql_select stopped in the {phase} phase: {reason} The goal stays open:{indentD (MessageData.ofGoal goal)}"

/-- Whether a term reads the query model: a declaration of the resolved query
({lit}`Belay.Sqlite.Model.Resolved`), such as {lit}`Resolved.Query.results`, a phase function such as
{lit}`Resolved.filtered`, or the scanned rows of a table ({lit}`Database.scanAt`). -/
def readsQueryModel (term : Expr) : Bool :=
  (term.find? fun part => match part.constName? with
    | some name => (`Belay.Sqlite.Model.Resolved).isPrefixOf name || name == ``Belay.Sqlite.Database.scanAt
    | none => false).isSome

/-- Whether the goal is about a query: its target or one of its hypotheses reads the query model
({name}`readsQueryModel`). -/
def aboutQuery (goal : MVarId) : MetaM Bool := goal.withContext do
  if readsQueryModel (← instantiateMVars (← goal.getType)) then return true
  (← getLCtx).anyM fun declaration => do
    if declaration.isImplementationDetail then return false
    return readsQueryModel (← instantiateMVars declaration.type)

/-- The refusal of a goal that is no claim about the results of a query. -/
def unknownShape : MessageData :=
  m!"sql_select proves a claim about the results of a query: returnsResult or returnsRows of a run, the \
    check of a query (Sql.check), or a goal whose target or hypotheses read the results or a phase of a \
    resolved query (Resolved) or the rows of a table (Database.scanAt). This goal is none of these, and no \
    hint applies to it. Use another tactic, or pass a rule as a hint."

/-- The procedure on one goal; the result is the goals that stay open. A goal that is no claim about the
results of a query, and to which no hint applies backward, is refused with an error. -/
partial def selectGoal (hints : Hints) (fuel : Nat) (goal : MVarId) (recognized : Bool := false) :
    TacticM (List MVarId) := do
  let (_, goal) ← goal.intros
  let target ← goal.withContext do whnfR (← instantiateMVars (← goal.getType))
  let isRun := target.isAppOf ``Belay.Sqlite.Run.returnsResult ||
    (target.isAppOfArity ``Belay.Sqlite.Sql.check 4 && (target.getArg! 1).isAppOf ``Belay.Sqlite.query)
  let recognized := recognized || isRun || (← aboutQuery goal)
  let phases := if isRun then [SelectPhase.execution] else []
  let mut refused : Option (Name × Expr) := none
  for rule in ← candidates hints phases do
    let term ← goal.withContext (ruleTerm rule)
    match ← applyBackward hints goal term with
    | .ok next => return ← selectGoal hints (fuel - 1) next true
    | .error (.premise type) =>
      if refused.isNone then refused := some ((match rule with | .inl name => name | .inr _ => `hint), type)
    | .error .noMatch => pure ()
  unless recognized || refused.isSome do throwError unknownShape
  let goal ← saturate hints fuel {} goal
  if ← finishLeaf hints goal then return []
  match refused with
  | some (rule, type) =>
    explain goal "execution" m!"the rule {rule} matches, but its premise{indentExpr type}\nis not proved."
  | none =>
    if isRun then
      explain goal "execution" m!"no execution rule matches the run, and no hint applies."
    else
      explain goal "result" m!"the facts that the rules give do not prove the goal. Prove it, or pass a rule or a \
        fact as a hint."
  return [goal]

/-- The procedure of {lit}`sql_select` with the given hints, as a sequence of steps of
{lit}`sql_select` on the main goal. -/
syntax (name := sqlSelect) "sql_select" (" [" term,* "]")? : tactic

/-- The number of rule applications in one run of {lit}`sql_select`. -/
def selectFuel : Nat := 64

/-- Run the procedure on the main goal; the goals that stay open replace it. -/
@[tactic sqlSelect] def evalSqlSelect : Tactic := fun written => do
  let hints : Hints := match written with
    | `(tactic| sql_select [$hints,*]) => hints.getElems
    | _ => #[]
  let goal ← getMainGoal
  replaceMainGoal (← selectGoal hints selectFuel goal)

end Belay.Sqlite.Select
