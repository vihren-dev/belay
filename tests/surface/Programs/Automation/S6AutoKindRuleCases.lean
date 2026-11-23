import Belay

/-! A fixture module of {lit}`tests/surface_s6_automation_test.py`: the cases of a kind rule that {lit}`sql_run`
must not take (statement rule pilot). A hint with a premise that it cannot close does not select the case of a
match: the tactic splits the match instead, and the proof stays complete. A continuing case with a choice between
results is not a single output, so {lit}`Belay.Sqlite.Run.ruleCases` keeps it unchanged, without an error. -/

set_option doc.verso true

namespace S6AutoKindRuleCases
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

set_option linter.unusedVariables false in
/-- For every context, statement, target, rows, resolution state and table: if the statement resolves to a plain
INSERT of the rows into the target and its step continues, the program that sends it checks a post that is always
true. The hint {lit}`present` gives the table only under a premise, so the tactic splits the match on the table
instead of a rewrite that would leave the premise open. The proof term does not use {lit}`present`, so the
linter of unused variables is off for it. -/
theorem conditional_hint_keeps_the_split (ctx : ExecutionContext) (stmt : Syntax.Statement) (target : Nat)
    (rows : List (List Resolved.Cell)) (after : ResolveState) (table : Table)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.insert target rows [] [] none, after))
    (present : True → ctx.connection.state.database.table target = some table)
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt []).continues = true) :
    (send ⟨[(stmt, [])]⟩).check (fun _ _ => True) ctx := by
  sql_run [found, present, modeled]
  all_goals trivial

/-- For every post that is always true, context, results and connection: a continuing case with the output
{lit}`.oneOf` stays as it is after {lit}`Belay.Sqlite.Run.ruleCases`, and it holds by the definition of
{name}`Sql.SendReached`. -/
theorem choice_case_stays (ctx : ExecutionContext) (results : List (List (List Value))) (next : Connection) :
    RunStep.Continuing (Sql.SendReached (fun _ _ => True) ctx) (.continued (.oneOf results) next []) := by
  run_tac do
    let goals ← Belay.Sqlite.Run.ruleCases #[] (← Lean.Elab.Tactic.getMainGoal)
    Lean.Elab.Tactic.setGoals goals
  guard_target =ₛ RunStep.Continuing (Sql.SendReached (fun _ _ => True) ctx) (.continued (.oneOf results) next [])
  intro found member _
  simp only [RunStep.executions, List.mem_singleton] at member
  subst member
  exact ⟨trivial, fun _ _ => trivial⟩

#print axioms conditional_hint_keeps_the_split
#print axioms choice_case_stays

end S6AutoKindRuleCases
