import PurgeFrameSchema

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_assertion_examples_test.py`: two-state claims of the guide's purge for
each database with the catalog of the pilot schema, proved with the tactics {lit}`sql_run` and {lit}`sql_holds`.
The first is the frame claim. The second says that the purge adds no session. -/

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The client statement of the guide's frame claim of the purge. Take
two values, NULL and text included. Take an admitted database with the catalog of {name}`sessions` and a complete
environment. Run the purge from the fresh start. After a run with no error, the reached database has each session of
the start that the filter did not select ({name}`purgeKeeps`, with the start as its initial database). A run with an
error requires nothing. The statement has no premise other than the catalog. Proof sketch: {lit}`sql_run` runs the
purge, and {lit}`sql_holds` brings the claim to an {lit}`EXCEPT` of rows of the two tables. The {lit}`EXCEPT` is empty
when each row of its first term is a row of the second ({name}`CompoundOperator.except_combine_eq_nil`): a row whose
condition is not 1 is not selected ({name}`Resolved.Expr.truthy_isNot_one`), so the delete keeps it
({name}`LiteralData.mem_deleted`). Two rows of the start that compare equal are identical, because their first cells
are distinct rowids ({name}`Resolved.equalRowsIdentical_rowidFirst`). -/
theorem purge_frame_on_sessions (c now : Value) :
    FreshEnsuresFrom (send (purge c now)) (·.HasCatalog sessions)
      (fun start => ifOk (holdsSince start (purgeKeeps c now))) := by
  refine (FreshEnsuresFrom.ifOk_iff _ _ _).2 ?_
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
  · refine CompoundOperator.except_combine_eq_nil _ _ _ fun output member => ?_
    simp only [List.mem_map, List.mem_filter, and_true] at member ⊢
    obtain ⟨cells, ⟨scanned, keep⟩, rfl⟩ := member
    refine ⟨cells, ?_, rfl⟩
    obtain ⟨row, inside, rfl⟩ := (mem_sourceRows_iff _ cells).1 scanned
    refine (mem_sourceRows_iff _ _).2 ⟨row, ?_, rfl⟩
    erw [Model.Database.rows_getD_setRows _ (Model.Database.position_lt_rows db.valid.admitted.rowsShaped found),
      LiteralData.mem_deleted]
    refine ⟨inside, ?_⟩
    have unselected := (Resolved.Expr.truthy_isNot_one (expression := purgeFilter) rfl .binary _ _).symm.trans keep
    rw [Bool.not_eq_true'] at unselected
    simp only [LiteralData.selected, Option.all_some]
    rw [← unselected]
    exact congrArg (fun pair => Resolved.truthy pair.1) (purgeFilter_rowwise.evaluate_congr _ _ row.values rfl)
  · have admitted := db.valid.admitted.table (Model.Database.table_of_sameCatalog schema 0 (by decide +kernel))
    exact Resolved.equalRowsIdentical_rowidFirst admitted.rowidsDistinct admitted.rowsAliased
      (by dsimp only; decide +kernel) .binary [.binary, .binary] _ [.column 1, .column 2]
      fun cells member => (List.mem_filter.1 member).1

/-- The claim that the purge adds no session: each row of {lit}`sessions` is a row of {lit}`before.sessions`. -/
def purgeAddsNone : Script :=
  sql r"SELECT 1 WHERE NOT EXISTS (SELECT * FROM sessions EXCEPT SELECT * FROM before.sessions)"

/-- Take two values, NULL and text included. Take an admitted database with the catalog of {name}`sessions` and a
complete environment. Run the purge from the fresh start. After a run with no error, each row of the reached table
{lit}`sessions` is a row of that table at the start ({name}`purgeAddsNone`). A run with an error requires nothing.
The statement has no premise other than the catalog. Proof sketch: as for {name}`purge_frame_on_sessions`, with the two
terms of the {lit}`EXCEPT` in the other order. Each row that the delete keeps is a row of the start
({name}`LiteralData.mem_deleted`). The reached database is valid, so its rows have distinct rowids. -/
theorem purge_adds_none (c now : Value) :
    FreshEnsuresFrom (send (purge c now)) (·.HasCatalog sessions)
      (fun start => ifOk (holdsSince start purgeAddsNone)) := by
  refine (FreshEnsuresFrom.ifOk_iff _ _ _).2 ?_
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
  · refine CompoundOperator.except_combine_eq_nil _ _ _ fun output member => ?_
    simp only [List.mem_map, List.mem_filter, and_true] at member ⊢
    obtain ⟨cells, scanned, rfl⟩ := member
    refine ⟨cells, ?_, rfl⟩
    obtain ⟨row, inside, rfl⟩ := (mem_sourceRows_iff _ cells).1 scanned
    erw [Model.Database.rows_getD_setRows _ (Model.Database.position_lt_rows db.valid.admitted.rowsShaped found),
      LiteralData.mem_deleted] at inside
    exact (mem_sourceRows_iff _ _).2 ⟨row, inside.1, rfl⟩
  · have admitted := valid.1.admitted.table
      (Model.Database.table_of_sameCatalog (database := Database.setRows db.raw sessionsEntry.1 _) schema 0 (by decide +kernel))
    exact Resolved.equalRowsIdentical_rowidFirst admitted.rowidsDistinct admitted.rowsAliased
      (by dsimp only; decide +kernel) .binary [.binary, .binary] _ [.column 1, .column 2]
      fun cells member => (List.mem_filter.1 member).1

#print axioms purge_frame_on_sessions
#print axioms purge_adds_none

end AssertionExamples
