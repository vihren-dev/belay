import S6RulesEffects
import S6RulesQueryPattern

/-! A fixture module of `tests/surface_s6_automation_test.py`: the tactic {lit}`sql_auto` (ADR 0017, S6). The
tactic tries {lit}`sql_commute`, then {lit}`sql_run` with the finishing steps of the SQL simp set, then
{lit}`grind`. Each proof below is closed by one route, and the info message holds the explicit steps of that
route as a replacement for the call. A fixture proves the same claim with the replacement alone, so the
replacement needs no search. The failing calls show the reasons of the routes and that the goal stays. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace S6RulesEffects
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- info: Try this:
  [apply]
    sql_run [rfl, ⟨_, _, _, rfl⟩]
    · intros; rfl -/
#guard_msgs (whitespace := lax) in
/-- For every complete environment, the update stores the new quantity. The route {lit}`sql_run` closes the
claim: the hints give the resolution and the model coverage, and evaluation gives the rows. -/
theorem bump_by_sql_auto :
    FreshEnsures (send bump) (fun db => db = sample)
      (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 6]]⌝ : ContextAssertion)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  sql_auto [rfl, ⟨_, _, _, rfl⟩]

/-- The claim of {name}`bump_by_sql_auto`, proved with the replacement that {lit}`sql_auto` offered. The proof
runs without a search. -/
theorem bump_by_replacement :
    FreshEnsures (send bump) (fun db => db = sample)
      (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 6]]⌝ : ContextAssertion)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  sql_run [rfl, ⟨_, _, _, rfl⟩]
  · intros; rfl

/-- info: Try this:
  [apply] grind -/
#guard_msgs (whitespace := lax) in
/-- A fact that is no claim about a SQL program is closed by the last route. The hint {lit}`given` names a
local hypothesis, which {lit}`grind` uses without a parameter, so the replacement has none. -/
theorem grind_route (rows : List Nat) (given : rows = [1, 2]) : rows.length = 2 := by
  sql_auto [given]

/-- error: sql_auto did not close the goal. The routes failed:
- sql_commute: sql_commute proves only a claim of Migration.PreservesAt or Migration.CommutesOn. Use another tactic for this goal.
- sql_run: sql_run proves a check of a SQL program, a triple, or the goal that mvcgen leaves for one. This goal is none of these. Use another tactic, or state the claim with Sql.check.
- grind: `grind` failed
Run one of these tactics alone to see the goals that it leaves. -/
#guard_msgs in
-- A false fact is closed by no route, and the message gives the reason of each route.
example : (1 : Nat) = 2 := by
  sql_auto

/-- warning: declaration uses `sorry` -/
#guard_msgs in
-- A failed call leaves the goal as it was: after try, the target is the original one. The example ends in
-- sorry on purpose, because no route proves the goal.
example : ∀ n : Nat, n = 0 := by
  try sql_auto
  guard_target =ₛ ∀ n : Nat, n = 0
  sorry

/-- info: Try this:
  [apply] grind -/
#guard_msgs (whitespace := lax) in
/-- The goals that follow the main goal stay after a call that closes the main goal. -/
theorem second_goal_stays_after_auto (rows : List Nat) (given : rows = [1, 2]) :
    rows.length = 2 ∧ True := by
  constructor
  sql_auto [given]
  exact True.intro

/-- error: sql_auto did not close the goal. The routes failed:
- sql_commute: sql_commute proves only a claim of Migration.PreservesAt or Migration.CommutesOn. Use another tactic for this goal.
- sql_run: it used the work limit of its share.
- grind: failed to generate equation theorems for `rfl`
Run one of these tactics alone to see the goals that it leaves. -/
#guard_msgs in
-- A route stops with the share of the work limit that it has. A claim that needs more work than the limit
-- allows is not closed, and the example is not admitted.
set_option maxHeartbeats 100 in
example : FreshEnsures (send bump) (fun db => db = sample)
    (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 6]]⌝ : ContextAssertion)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  sql_auto [rfl, ⟨_, _, _, rfl⟩]

#print axioms bump_by_sql_auto
#print axioms bump_by_replacement
#print axioms grind_route
#print axioms second_goal_stays_after_auto

end S6RulesEffects

namespace S6RulesQueryPattern
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- info: Try this:
  [apply] sql_commute [analysis, obligations] -/
#guard_msgs (whitespace := lax) in
/-- For every bound value, the lookup is preserved by the migration. The first route closes the claim. -/
theorem lookup_preserved_by_sql_auto (name : Value) :
    Migration.PreservesAt (send expansion) (fun _ => True) (send (lookup name)) initial := by
  sql_auto [analysis, obligations]

#print axioms lookup_preserved_by_sql_auto

end S6RulesQueryPattern
