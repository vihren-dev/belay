import PurgeFrameSchema

set_option doc.verso true

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the effect claim of the guide's purge for each
database with the catalog of the pilot schema, proved with the tactics {lit}`sql_run` and {lit}`sql_holds`. The
overview with checked names is at the end of the file. -/

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The effect claim of the purge: no session is left that the filter of the purge selects with the two values. -/
def purgeClears (c now : Value) : Script :=
  sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions WHERE customer_id = $c AND expires_at < $now)"

/-- The client statement of the effect claim of the purge. Take two values, NULL and text included. Take an admitted
database with the catalog of {name}`sessions` and a complete environment. Run the purge from the fresh start. If the
run has no error, the reached database has no session that the filter of the purge selects ({name}`purgeClears`). A
run with an error requires nothing. The statement has no premise other than the catalog. Proof sketch: {lit}`sql_run`
runs the purge, and {lit}`sql_holds` brings the claim to the rows of the reached table. A reached row is a row that
the delete keeps ({name}`LiteralData.mem_deleted`), so the filter is not true for it in the context of the delete. The
row-wise filter has the same value with the two values alone ({name}`Resolved.Expr.Rowwise.evaluate_congr`). -/
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
  sql_holds [schema]
  intro values member
  erw [Model.Database.rows_getD_setRows _ (Model.Database.position_lt_rows db.valid.admitted.rowsShaped found)]
    at member
  obtain ⟨row, kept, rfl⟩ := (mem_sourceRows_iff _ _).1 member
  rw [LiteralData.mem_deleted] at kept
  rw [← kept.2]
  exact congrArg (fun pair => Resolved.truthy pair.1) (purgeFilter_rowwise.evaluate_congr _ _ row.values rfl)

#print axioms purge_clears

/-! The claim {name}`purgeClears` says that no session is left that the filter of the purge selects. Its client
statement {name}`purge_clears` has no premise other than the catalog. After {lit}`sql_run` and {lit}`sql_holds`, the
proof reasons only about the rows that a delete keeps ({name}`LiteralData.mem_deleted`). -/

end AssertionExamples
