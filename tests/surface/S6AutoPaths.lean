import S6RulesEffects

/-! A fixture module of `tests/surface_s6_automation_test.py`: the paths of {lit}`sql_run` that
{lit}`S6AutoEffects` does not reach (ADR 0017, S6): a DELETE, an ADD COLUMN, a query of rows, a single value, a
sent SELECT whose output is a choice, and a goal that has sibling goals. Each claim is about the one database
{name}`S6RulesEffects.sample`. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace S6RulesEffects
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The delete of the item with a given id. -/
def purge : Script := sql r"DELETE FROM items WHERE id = ?1" (Value.integer 1)

/-- For every complete environment, every run of the delete that has no error ends with no rows in the items
table. The claim holds for the one database {name}`sample`. Proof sketch: {lit}`sql_run` applies
{name}`Sql.check_send_plainDelete`; the hints close the resolution and the model coverage, and evaluation gives
the rows. -/
theorem purge_empties_items :
    FreshEnsures (send purge) (fun db => db = sample)
      (ifOk (fun final => ⌜tableValues 0 final.connection = []⌝ : ContextAssertion)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  sql_run [rfl, ⟨_, _, _, rfl⟩]
  all_goals (intro _; rfl)

/-- The column that the migration adds. -/
def widen : Script := sql r"ALTER TABLE items ADD COLUMN note TEXT"

/-- For every complete environment, every run of the ADD COLUMN that has no error ends with the one item row
extended by a NULL cell. The claim holds for the one database {name}`sample`. Proof sketch: {lit}`sql_run`
applies {name}`Sql.check_send_addColumn`; the premise that gives the default value is closed by the fact that a
column without a default reads NULL, and evaluation gives the rows. -/
theorem widen_adds_null_cells :
    FreshEnsures (send widen) (fun db => db = sample)
      (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 5, .null]]⌝ : ContextAssertion)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  sql_run [rfl, ⟨_, _, _, rfl⟩]
  case success =>
    have stored := clockRead rfl
    have plain : default = Value.null := by
      have same := stored.symm.trans (by rfl)
      exact Except.ok.inj same
    subst plain
    intro _
    rfl

/-- The read of all quantities. -/
def quantities : Script := sql r"SELECT qty FROM items"

/-- The property that the reads below have: for every value, the connection at the end is the connection at the
start. -/
def keepsConnection {α : Type} (env : Env) (_ : α) (final : ExecutionContext) : Prop :=
  final.connection = (ExecutionContext.initial sample env).connection

/-- The one statement of the read. -/
def quantitiesStatement : Syntax.Statement := (quantities.statements.head (by decide +kernel)).1

set_option maxHeartbeats 4000000 in
/-- For every complete environment, the model runs the read at the initial context of {name}`sample` to a step
that continues. Proof sketch: evaluation of the step; the environment does not matter to a read of a table. -/
theorem quantities_modeled (env : Env) :
    ∃ output next others, runScriptStep runContext (ExecutionContext.initial sample env).clock
      (ExecutionContext.initial sample env).index (ExecutionContext.initial sample env).connection
      quantitiesStatement [] = .continued output next others := ⟨_, _, _, rfl⟩

/-- For every complete environment, the program that reads the rows of the items table ends with the
connection that it started with. Proof sketch: {lit}`sql_run` applies {name}`Sql.check_query_select`. -/
theorem query_keeps_connection (env : Env) :
    (query quantities).check (keepsConnection env) (ExecutionContext.initial sample env) := by
  sql_run [quantities_modeled env]
  all_goals (intros; rfl)

/-- For every complete environment, the program that reads one value of the items table ends with the
connection that it started with. Proof sketch: {lit}`sql_run` applies {name}`Sql.check_single_select`. -/
theorem single_keeps_connection (env : Env) :
    (single quantities).check (keepsConnection env) (ExecutionContext.initial sample env) := by
  sql_run [quantities_modeled env]
  all_goals (intros; rfl)

/-- For every complete environment, the program that sends the read of the items table ends with the
connection that it started with. The output of a sent SELECT is a choice between results. Proof sketch:
{lit}`sql_run` applies {name}`Sql.check_send_select`. -/
theorem sent_select_keeps_connection (env : Env) :
    (send quantities).check (keepsConnection env) (ExecutionContext.initial sample env) := by
  sql_run [quantities_modeled env]
  all_goals (intros; rfl)

/-- Two goals at once: {lit}`sql_run` works on the first goal while the second goal is visible, and the second
goal is still there, after the one obligation of the first, when the tactic is done. -/
theorem second_goal_stays (env : Env) :
    (query quantities).check (keepsConnection env) (ExecutionContext.initial sample env) ∧
    (single quantities).check (keepsConnection env) (ExecutionContext.initial sample env) := by
  constructor
  sql_run [quantities_modeled env]
  · intros
    rfl
  · exact single_keeps_connection env

#print axioms purge_empties_items
#print axioms widen_adds_null_cells
#print axioms query_keeps_connection
#print axioms single_keeps_connection
#print axioms sent_select_keeps_connection
#print axioms second_goal_stays

end S6RulesEffects
