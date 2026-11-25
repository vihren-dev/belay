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
  sql_run [rfl]
  all_goals (intro _; rfl)

/-- The claim of {name}`bump_stores_new_quantity_by_sql_run`, proved with {name}`Sql.check_send_of_rule` and the plain UPDATE rule. -/
theorem bump_stores_new_quantity_by_rules :
    FreshEnsures (send bump) (fun db => db = sample)
      (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 6]]⌝ : ContextAssertion)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  refine Sql.check_send_of_rule (runScriptStep_plainUpdate_eq (statement := bumpStatement)
    (target := 0) (subqueries := []) (assignments := _) (filter := _) (by rfl))
    (ExecutionContext.initial_holds_valid sample env) rfl ?_
  exact Sql.sendReached_single (fun _ same => by cases same) (fun _ _ => rfl)


/-- For every valid starting context and modeled plain UPDATE, the send reports a change count
or reports an error and keeps the starting database. This includes updates that read subqueries.
Proof sketch: the resolution selects the exact UPDATE rule. The two continuing cases give the
count and the unchanged database on failure. -/
theorem update_count_or_failure (ctx : ExecutionContext) (statement : Syntax.Statement) (values : List Value)
    (target : Nat) (assignments : List (Nat × Resolved.Expr)) (filter : Option Resolved.Expr)
    (subqueries : List Resolved.Query) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState statement =
      .ok (.update target assignments filter [] subqueries none, after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection statement values).continues = true) :
    (send ⟨[(statement, values)]⟩).check (fun outputs final =>
      (∃ count, outputs = [.done count]) ∨
      ((∃ code, outputs = [.error code]) ∧ final.connection.state.database = ctx.connection.state.database)) ctx := by
  sql_run
  case success => exact Or.inl ⟨_, rfl⟩
  case failure => exact Or.inr ⟨⟨_, rfl⟩, rfl⟩

#print axioms update_count_or_failure
#print axioms bump_stores_new_quantity_by_sql_run
#print axioms bump_stores_new_quantity_by_rules

end S6RulesEffects
