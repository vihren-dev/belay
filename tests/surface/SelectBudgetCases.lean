import SelectProcedureCases

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_select_procedure_test.py`: the work limit and the cancellation
of {lit}`sql_auto` on claims that its route {lit}`sql_select` proves (B06). A call that runs out of its
work limit, or that is cancelled inside a route, fails and leaves the goal and its siblings as they were, with no
assignment; the proof then closes them by other steps. The procedure of {lit}`sql_select` inside the
route {lit}`sql_run` shares the share of that route: it does not get a new limit. -/

namespace SelectBudgetCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases
open Lean Elab Tactic

/-- The outcome of a tactic: its value, or the exception that it throws, also an interruption, which
{lit}`try` and {lit}`tryCatchRuntimeEx` pass on. -/
def outcomeOf {α : Type} (action : TacticM α) : TacticM (Except Exception α) :=
  fun a b c d e f g h => BaseIO.toEIO (action a b c d e f g h).toBaseIO

/-- A hint that cancels the elaboration that reads it: it sets the cancellation token of the elaboration,
when there is one, and stands for {lean}`True.intro`. {lit}`sql_commute` and {lit}`sql_run` do not read
the hints of a claim about a run, so in {lit}`sql_auto` the procedure of {lit}`sql_select` reads it first,
after the earlier routes have run; on a check, the procedure that {lit}`sql_run` gives the check to reads
it. -/
elab "cancel_now%" : term => do
  if let some token := (← readThe Core.Context).cancelTk? then token.set
  return mkConst ``True.intro

/-- Run a tactic on the goals with a work limit, in thousands of heartbeats, or, for {lean}`none`, with a
cancellation token that is not set yet, which a hint {lit}`cancel_now%` sets during the call. The
tactic must fail and leave the goals unchanged and unassigned; the message of the failure, or
{lit}`interrupted` for an interruption after the token was set, is logged as information. -/
def failsAndRestores (limit : Option Nat) (tactic : TSyntax `tactic) : TacticM Unit := do
  let before ← getGoals
  let token ← IO.CancelToken.new
  let outcome ← outcomeOf <| withTheReader Core.Context (fun context => match limit with
      | some units => { context with maxHeartbeats := units * 1000 }
      | none => { context with cancelTk? := some token })
    (withCurrHeartbeats (evalTactic tactic))
  let .error error := outcome | throwError "the tactic closed the goal"
  unless (← getGoals) == before do throwError "the goals changed"
  for goal in before do
    if ← goal.isAssigned then throwError "a goal was assigned"
  if error.isInterrupt && !(← token.isSet) then throwError "an interruption came before the hint"
  logInfo (if error.isInterrupt then m!"interrupted" else error.toMessageData)

/-- info: sql_auto did not close the goal. The routes failed:
- sql_commute: sql_commute proves only a claim of Migration.PreservesAt or Migration.CommutesOn. Use another tactic for this goal.
- sql_run: sql_run proves a check of a SQL program, a triple, or the goal that mvcgen leaves for one. This goal is none of these. Use another tactic, or state the claim with Sql.check.
- sql_select: it used the work limit of its share.
- grind: `grind` failed
Run one of these tactics alone to see the goals that it leaves. -/
#guard_msgs in
/-- A08 with a sibling goal: with a work limit of 300 thousand heartbeats, {lit}`sql_auto` does not close
the claim, and the claim and the sibling goal stay as they were. The proof then closes the claim with
{name}`SelectProcedureCases.count_rows`. -/
theorem count_after_limit (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query SelectCountCases.countAll SelectCountCases.countAll_one) env).returnsResult
      (· = [[.integer (db.scanAt 0).length]]) ∧ True := by
  constructor
  run_tac failsAndRestores (some 300) (← `(tactic| sql_auto [$(mkIdent `schema)]))
  · exact SelectProcedureCases.count_rows db env schema
  · trivial

/-- info: interrupted -/
#guard_msgs in
/-- The claim of {name}`count_after_limit` when the call is cancelled inside the route {lit}`sql_select`:
the interruption passes through the route and through {lit}`sql_auto`, and the claim and the sibling goal
stay as they were. -/
theorem count_after_cancel (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query SelectCountCases.countAll SelectCountCases.countAll_one) env).returnsResult
      (· = [[.integer (db.scanAt 0).length]]) ∧ True := by
  constructor
  run_tac failsAndRestores none (← `(tactic| sql_auto [$(mkIdent `schema), cancel_now%]))
  · exact SelectProcedureCases.count_rows db env schema
  · trivial

/-- info: Replace sql_auto with its steps:
  [apply] sql_run [schema] -/
#guard_msgs (whitespace := lax) in
/-- A08 as a check at the initial context: without a work limit, the route {lit}`sql_run` closes the
claim; it gives the check of the query to {lit}`sql_select`. -/
theorem count_check (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (query SelectCountCases.countAll SelectCountCases.countAll_one).check
      (fun result _ => result = .ok [[.integer (db.scanAt 0).length]]) (ExecutionContext.initial db env) := by
  sql_auto [schema]

/-- info: sql_auto did not close the goal. The routes failed:
- sql_commute: sql_commute proves only a claim of Migration.PreservesAt or Migration.CommutesOn. Use another tactic for this goal.
- sql_run: it used the work limit of its share.
- sql_select: it used the work limit of its share.
- grind: `grind` failed
Run one of these tactics alone to see the goals that it leaves. -/
#guard_msgs in
/-- The claim of {name}`count_check` with a work limit of 300 thousand heartbeats: the procedure of
{lit}`sql_select` inside the route {lit}`sql_run` uses the share of that route and runs out with it, so
the route fails; no route gets a new limit. The goal stays as it was. -/
theorem count_check_after_limit (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (query SelectCountCases.countAll SelectCountCases.countAll_one).check
      (fun result _ => result = .ok [[.integer (db.scanAt 0).length]]) (ExecutionContext.initial db env) := by
  run_tac failsAndRestores (some 300) (← `(tactic| sql_auto [$(mkIdent `schema)]))
  exact count_check db env schema

/-- info: interrupted -/
#guard_msgs in
/-- The claim of {name}`count_check` when the call is cancelled inside the procedure that the route
{lit}`sql_run` gives the check to: the interruption passes through the attempt of that procedure, which
restores its state only for an ordinary failure, and the goal stays as it was. -/
theorem count_check_after_cancel (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (query SelectCountCases.countAll SelectCountCases.countAll_one).check
      (fun result _ => result = .ok [[.integer (db.scanAt 0).length]]) (ExecutionContext.initial db env) := by
  run_tac failsAndRestores none (← `(tactic| sql_auto [$(mkIdent `schema), cancel_now%]))
  exact count_check db env schema

end SelectBudgetCases

#print axioms SelectBudgetCases.count_after_limit
#print axioms SelectBudgetCases.count_after_cancel
#print axioms SelectBudgetCases.count_check
#print axioms SelectBudgetCases.count_check_after_limit
#print axioms SelectBudgetCases.count_check_after_cancel
