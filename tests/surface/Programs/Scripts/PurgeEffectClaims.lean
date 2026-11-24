import PurgeFrameSchema
import SelectOneWhereSupport

set_option doc.verso true

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the effect claim of the guide's purge for each
database with the catalog of the pilot schema. The overview with checked names is at the end of the file. -/

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The effect claim of the purge: no session is left that the filter of the purge selects with the two values. -/
def purgeClears (c now : Value) : Script :=
  sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions WHERE customer_id = $c AND expires_at < $now)"

/-- Take a database with the catalog of {name}`sessions` and two values. The effect claim holds on the database
exactly when the filter of the purge, with the two values, is true for no row of the table {lit}`sessions`. Proof
sketch: the claim resolves to {lit}`SELECT 1 WHERE NOT EXISTS` over the subquery of the table with the filter
({name}`resolveStatement_selectOne_notExists`). The kernel decides the lookup and the resolution of the filter on the
catalog of {name}`sessions`. {name}`whereOne_claims` reduces the claim to the truth of {lit}`NOT EXISTS`.
{name}`tableOne_run` shows that the subquery has no fault and that it is empty exactly when the filter is true for
no row. -/
theorem purgeClears_iff (db : Database) (schema : db.HasCatalog sessions) (c now : Value) :
    Holds (purgeClears c now) db ↔
      ∀ row ∈ Resolved.sourceRows ⟨sessionsEntry.2, db.raw.rows.getD sessionsEntry.1 []⟩,
        Resolved.truthy (purgeFilter.eval (.bound [c, now]) row) = false := by
  have calm : ∀ expression ∈ (some purgeFilter).toList, expression.Calm := by
    simpa using purgeFilter_rowwise.calm
  have run := tableOne_run db [c, now] (name! "sessions") sessionsEntry.1 sessionsEntry.2 (some purgeFilter)
    (sessions_found db schema) calm
  have claims := whereOne_claims (script := purgeClears c now) (isQuery := rfl) _ [c, now] rfl db
    (.not (.exists 0)) (tableOne sessionsEntry.1 (some purgeFilter))
    (by
      rw [Database.resolveState_of_catalog db sessions schema]
      exact resolveStatement_selectOne_notExists runContext _ _ _ sessionsEntry.1 sessionsEntry.2 (some purgeFilter)
        rfl rfl rfl (by decide +kernel) (.inr ⟨_, _, none, rfl, rfl, by decide +kernel, by decide +kernel⟩))
    (Resolved.Statement.Calm.selectOne_subquery _ _ _ _ _
      ((Resolved.Expr.calm_not _).2 (Resolved.Expr.calm_exists _)) calm (Resolved.Expr.calm_literal _))
    (by rw [Resolved.Expr.fault_not, Resolved.Expr.fault_exists, Resolved.EvalContext.statement_one]; exact run.1)
  rw [claims.1, Resolved.Expr.eval_not, Resolved.truthy_not, Resolved.Expr.eval_exists,
    Resolved.EvalContext.statement_one, run.2]
  simp [someRow, Resolved.falsy]

/-- The client statement of the effect claim of the purge. Take two values, NULL and text included. Take an admitted
database with the catalog of {name}`sessions` and a complete environment. Run the purge from the fresh start. If the
run has no error, the reached database has no session that the filter of the purge selects ({name}`purgeClears`). A
run with an error requires nothing. The statement has no premise other than the catalog. Proof sketch: the step of
the purge continues ({name}`PurgeFrameSite.purge_continues`). It stores the rows that {name}`LiteralData.deleted`
keeps ({name}`runScriptStep_plainDelete_eq`). {name}`purgeClears_iff` reduces the claim to the rows of the reached
table. The delete keeps a row only when the filter is not true for it in the context of the statement. The row-wise
filter has the same value with the two values alone ({name}`Resolved.Expr.Rowwise.evaluate_congr`). -/
theorem purge_clears (c now : Value) :
    FreshEnsures (send (purge c now)) (·.HasCatalog sessions) (ifOk (holds (purgeClears c now))) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  intro db schema env _complete
  rw [purge_script]
  have found : db.raw.catalog.findTable (name! "sessions") = some (sessionsEntry.1, sessionsEntry.2) :=
    sessions_found db schema
  have present := Database.table_of_findTable db.raw _ _ _ found
  have resolves : resolveStatement runContext (db.raw.connection {}).resolveState purgeStatement =
      .ok (.delete sessionsEntry.1 (some purgeFilter) [] [] none, (sessions.raw.connection {}).resolveState) :=
    (sessionsSite db schema).purgeResolves
  sql_run [resolves, (sessionsSite db schema).purge_continues env c now, present]
  intro _allOk
  have aligned := Model.Database.position_lt_rows db.valid.admitted.rowsShaped found
  refine (Holds.reached_iff_holds_of_valid _ _ _ valid.1).2 ((purgeClears_iff ⟨_, valid.1⟩ schema c now).2 ?_)
  intro values member
  simp only [Connection.afterWrite, ExecutionContext.initial, Database.Raw.connection] at member
  rw [Model.Database.rows_getD_setRows _ aligned] at member
  obtain ⟨row, kept, rfl⟩ := (mem_sourceRows_iff _ _).1 member
  simp only [LiteralData.deleted, LiteralData.selected, List.mem_filter, Option.all_some,
    Bool.not_eq_true'] at kept
  rw [← kept.2]
  exact congrArg (fun pair => Resolved.truthy pair.1) (purgeFilter_rowwise.evaluate_congr _ _ row.values rfl)

#print axioms purgeClears_iff
#print axioms purge_clears

/-! The claim {name}`purgeClears` says that no session is left that the filter of the purge selects. Its client
statement {name}`purge_clears` has no premise other than the catalog. The proof uses the laws of the query form
{lit}`SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM t WHERE f)`: {name}`resolveStatement_selectOne_notExists`,
{name}`tableOne_run` and {name}`whereOne_claims`. -/

end AssertionExamples
