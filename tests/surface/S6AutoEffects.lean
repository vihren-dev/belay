import S6RulesEffects

/-! A fixture module of `tests/surface_s6_automation_test.py`: the claims of {lit}`S6RulesEffects` about an UPDATE
and an ADD COLUMN, proved with the tactic {lit}`sql_run` and, for each claim, with the public step rules alone
(ADR 0017, S6). The tactic leaves the premises that it cannot close from its hints; here the hints are
{lit}`rfl`, which evaluates the resolution of the statement and the table of the one database, and a witness
that the model runs the statement. The goal that remains states the rows after the statement. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace S6RulesEffects
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The claim of {name}`bump_stores_new_quantity`, proved with {lit}`sql_run`. The goal that remains after the
tactic is the final property for an update without an error; the rows are computed by evaluation. -/
theorem bump_stores_new_quantity_by_sql_run :
    FreshEnsures (send bump) (fun db => db = sample)
      (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 6]]⌝ : ContextAssertion)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  sql_run [rfl, ⟨_, _, _, rfl⟩]
  all_goals (intro _; rfl)

/-- The claim of {name}`bump_stores_new_quantity_by_sql_run`, proved with {name}`Sql.check_send_plainUpdate`. -/
theorem bump_stores_new_quantity_by_rules :
    FreshEnsures (send bump) (fun db => db = sample)
      (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 6]]⌝ : ContextAssertion)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  obtain ⟨after, found⟩ : ∃ after, resolveStatement runContext (sample.raw.connection env.counters).resolveState
      bumpStatement = .ok (bumpResolved, after) := ⟨_, rfl⟩
  have modeled : RunStep.continues (runScriptStep runContext env.clock 0 (sample.raw.connection env.counters)
      bumpStatement [.integer 1]) = true := rfl
  refine Sql.check_send_plainUpdate (statement := bumpStatement) (values := [.integer 1])
    (ExecutionContext.initial_holds_valid sample env) found sample_items (RunStep.continues_iff.1 modeled) ?_ ?_
  · intro output value next noError ongoing timed same valid
    subst same
    intro _
    rfl
  · intro output value next failed ongoing same valid allOk
    simp [List.allOk, ExecutionContext.next, failed] at allOk

#print axioms bump_stores_new_quantity_by_sql_run
#print axioms bump_stores_new_quantity_by_rules

end S6RulesEffects
