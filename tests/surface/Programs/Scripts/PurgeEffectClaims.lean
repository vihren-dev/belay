import PurgeFrameSchema

set_option doc.verso true

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the effect claim of the guide's purge for each
database with the catalog of the pilot schema. The overview with checked names is at the end of the file. -/

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The effect claim of the purge: no session is left that the filter of the purge selects with the two values. -/
def purgeClears (c now : Value) : Script :=
  sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions WHERE customer_id = $c AND expires_at < $now)"

/-- The syntax tree of the effect claim, which does not depend on the two values. -/
def purgeClearsStatement : Syntax.Statement := ((purgeClears .null .null).statements.headD (.begin, [])).1

/-- The subquery of the effect claim as the model resolves it: {lit}`SELECT 1 FROM sessions WHERE f` with the filter
of the purge. -/
def purgeClearsSubquery : Resolved.Query :=
  Resolved.Query.simple [.first sessionsEntry.1] (some purgeFilter) ([Resolved.Expr.literal (.integer 1)].map .scalar)
    ["1"]

/-- Take a database with the catalog of {name}`sessions` and two values. The effect claim holds on the database
exactly when the filter of the purge, with the two values, is true for no row of the table {lit}`sessions`. Proof
sketch: the kernel decides the resolution of the claim on the catalog of {name}`sessions`, and
{name}`Holds.inContext_iff_hasRows` gives the output of the resolved statement. The laws of the parts then apply in
turn: {lit}`SELECT 1 WHERE` ({name}`resolvedStepOutput_selectOneWhere_hasRows`), {lit}`NOT EXISTS`
({name}`Resolved.Expr.truthy_notExists`), the subquery of the statement ({name}`Resolved.statementContext_subqueries`)
and the read of the table ({name}`Resolved.Query.simple_subqueryRun`). The row-wise filter has the same value in the
context of the subquery as with the two values alone ({name}`Resolved.Expr.Rowwise.evaluate_congr`). -/
theorem purgeClears_iff (db : Database) (schema : db.HasCatalog sessions) (c now : Value) :
    Holds (purgeClears c now) db ↔
      ∀ row ∈ Resolved.sourceRows ⟨sessionsEntry.2, db.raw.rows.getD sessionsEntry.1 []⟩,
        Resolved.truthy (purgeFilter.eval (.bound [c, now]) row) = false := by
  have present := Database.table_of_findTable db.raw _ _ _ (sessions_found db schema)
  have read := fun context => Resolved.Query.simple_subqueryRun context db.raw [] none _ _ [.literal (.integer 1)] _
    (Resolved.Query.source_first_from _ purgeClearsSubquery _ _ _ _ rfl present) rfl rfl
    (fun row _ expression member => by
      simp [Resolved.Query.expressions, Resolved.Query.keptExpressions, Resolved.Query.simple,
        Resolved.QuerySource.first, Resolved.QuerySource.expressions, Resolved.Output.scalars,
        Resolved.Output.operands] at member
      rcases member with rfl | rfl
      · exact purgeFilter_rowwise.fault_none context row
      · rfl)
  rw [← Holds.inContext_observation_iff, Holds.inContext_iff_hasRows (script := purgeClears c now) (statement := purgeClearsStatement)
      (parameters := [c, now]) _ _ rfl (by
      show resolveStatement runContext (db.raw.connection {}).resolveState purgeClearsStatement = _
      rw [Database.resolveState_of_catalog db sessions schema]
      exact (by decide +kernel : resolveStatement runContext (sessions.raw.connection {}).resolveState
        purgeClearsStatement = .ok (.query (Resolved.Query.selectOneWhere (.not (.exists 0))) [purgeClearsSubquery],
          (sessions.raw.connection {}).resolveState))),
    resolvedStepOutput_selectOneWhere_hasRows _ _ _ _ _ _ none
      (fun expression member => Resolved.Expr.calm_of_calmCheck (List.all_eq_true.mp (by decide +kernel) _ member))
      (by rw [Resolved.Expr.fault_not, Resolved.Expr.fault_exists,
        Resolved.statementContext_subqueries _ _ _ _ _ _ _ _ rfl]; exact (read _).2.1),
    Resolved.Expr.truthy_notExists, Resolved.statementContext_subqueries _ _ _ _ _ _ _ _ rfl]
  unfold purgeClearsSubquery
  simp only [Database.Raw.observationContext, Database.Raw.connection]
  rw [(read _).1]
  simp only [List.isEmpty_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff, Option.all_some, Bool.not_eq_true]
  refine forall₂_congr fun row _ => ?_
  simp only [Resolved.Expr.eval]
  exact Iff.of_eq (congrArg (fun pair => Resolved.truthy pair.1 = false)
    (purgeFilter_rowwise.evaluate_congr _ _ row (by rfl)))

/-- The client statement of the effect claim of the purge. Take two values, NULL and text included. Take an admitted
database with the catalog of {name}`sessions` and a complete environment. Run the purge from the fresh start. If the
run has no error, the reached database has no session that the filter of the purge selects ({name}`purgeClears`). A
run with an error requires nothing. The statement has no premise other than the catalog. Proof sketch: the step of
the purge continues ({name}`PurgeFrameSite.purge_continues`). It stores the rows that {name}`LiteralData.deleted`
keeps ({name}`runScriptStep_plainDelete_eq`). {name}`purgeClears_iff` reduces the claim to the rows of the reached
table. The delete keeps a row only when the filter is not true for it in the context of the statement
({name}`LiteralData.mem_deleted`). The row-wise
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
  rw [LiteralData.mem_deleted] at kept
  rw [← kept.2]
  exact congrArg (fun pair => Resolved.truthy pair.1) (purgeFilter_rowwise.evaluate_congr _ _ row.values rfl)

#print axioms purgeClears_iff
#print axioms purge_clears

/-! The claim {name}`purgeClears` says that no session is left that the filter of the purge selects. Its client
statement {name}`purge_clears` has no premise other than the catalog. The proof composes the laws of the parts of the
claim: the bridge {name}`Holds.inContext_iff_hasRows`, {lit}`SELECT 1 WHERE`
({name}`resolvedStepOutput_selectOneWhere_hasRows`), {lit}`NOT EXISTS` ({name}`Resolved.Expr.truthy_notExists`), the
read of one table ({name}`Resolved.Query.simple_subqueryRun`) and the rows that a delete keeps
({name}`LiteralData.mem_deleted`). The proof of the frame claim uses the same laws. -/

end AssertionExamples
