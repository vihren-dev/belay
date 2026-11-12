import PurgeFrameSite

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the guide's purge frame claim as a fresh-run
triple over every admitted database (ADR 0017, S6). For every pair of values, also NULL and text, a purge that
succeeds leaves every session of the start that is not an expired session of the customer, when the schema, the
resolution and the model of the purge are as the fields of `PurgeFrameSite` say. The claim compares the reached
database with the captured start through the schema `before`, and uses the NULL-aware condition `IS NOT 1`. -/

set_option doc.verso true

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- For every database with the site of the purge, values, and reached database that holds the rows that the delete of
the purge keeps, the two-state observation of the claim over the start and the reached database has rows. In plain
words: every row of the start for which the condition is not 1 is still in the reached table. Proof sketch: the
observation resolves the claim against the catalog of the start and the reached catalog, which the delete does not
change ({name}`PurgeFrameSite.claimResolves`); {name}`resolvedStepOutput_notExistsExcept_hasRows` reduces the rows to
two facts about the tables. A row with a condition that is not 1 is not selected by the filter, whatever the values
are ({name}`Resolved.Expr.truthy_isNot_one_and`), so the delete keeps it
({name}`Resolved.notExistsExcept_subset`); and the first cell of a row is its rowid, which no other row shares, so the
rows of the first term are identical where they compare equal ({name}`Resolved.notExistsExcept_identical`). -/
theorem purge_keeps_rows {db : Database} {c now : Value} (site : PurgeFrameSite db c now)
    (deleteContext : Resolved.EvalContext) (parameters : deleteContext.parameters = [c, now]) :
    ((purgeKeeps c now).observeTwoStateIn db.raw
      (Database.Raw.observationContext (db.raw.setRows site.position
        (LiteralData.deleted deleteContext ⟨site.table, db.raw.rows.getD site.position []⟩ (some purgeFilter)).rows))).hasRows =
      true := by
  have present := Database.table_of_findTable db.raw _ site.position site.table site.found
  have aligned := Model.Database.position_lt_rows db.valid.admitted.rowsShaped site.found
  have admitted := db.valid.admitted.table present
  unfold Script.observeTwoStateIn
  rw [purgeKeeps_script]
  simp only [purgeKeepsStatement_asQuery]
  unfold Model.observeTwoState
  rw [show (Database.Raw.observationContext (db.raw.setRows site.position
    (LiteralData.deleted deleteContext ⟨site.table, db.raw.rows.getD site.position []⟩ (some purgeFilter)).rows)).connection.state.database.catalog =
      db.raw.catalog from rfl, site.claimResolves]
  simp only [purgeKeeps_usesSchema, ite_true]
  refine resolvedStepOutput_notExistsExcept_hasRows 0 _ [c, now] db.raw _ site.position purgeKeepsCondition
    [.column 0, .column 1, .column 2] site.names [.binary, .binary, .binary] _
    ⟨site.table, (LiteralData.deleted deleteContext ⟨site.table, db.raw.rows.getD site.position []⟩ (some purgeFilter)).rows⟩
    (purgeKeepsCompound_shape site.names) purgeKeepsCondition_rowwise sessionColumns_rowwise present
    (Model.Database.table_setRows _ present aligned) ?_ ?_
  · refine Resolved.notExistsExcept_subset site.position purgeKeepsCondition sessionColumns site.names _ purgeFilter
      deleteContext _ ?_
    intro row _ kept
    have rowwise := purgeFilter_rowwise.evaluate_congr deleteContext (Resolved.EvalContext.bound [c, now]) row.values
      (by simp [parameters])
    have not_selected := Resolved.Expr.truthy_isNot_one_and _ _ _ row.values kept
    show Resolved.truthy ((purgeFilter.evaluate deleteContext row.values).1) = false
    rw [rowwise]
    exact not_selected
  · exact Resolved.notExistsExcept_identical site.position purgeKeepsCondition (.column 0) [.column 1, .column 2]
      site.names .binary [.binary, .binary] _ _ admitted.rowidsDistinct admitted.rowsAliased site.keyAlias rfl

/-- The guide's frame claim of the purge, for every pair of values: for every admitted database with the site of the
purge and every complete environment, every run of the purge from the fresh start that has no error ends in a database
in which every session of the start that is not an expired session of the customer is still there. The values may be
NULL or text. The claim reads the start through {lit}`before` and states the unchanged rows with the condition
{lit}`IS NOT 1`, so a NULL parameter does not weaken it. A purge that fails requires nothing, and the model's rollback
decides what a failed run leaves. Proof sketch: the check of the one statement; the plain delete stores the rows that
{name}`LiteralData.deleted` keeps ({name}`Sql.ifOk_send_plainDelete`), and {name}`purge_keeps_rows` shows that
the observation of the claim over the start and that database has rows. -/
theorem purge_frame (c now : Value) :
    FreshEnsuresFrom (send (purge c now)) (fun db => Nonempty (PurgeFrameSite db c now))
      (fun start => ifOk (holdsSince start (purgeKeeps c now))) := by
  refine (FreshEnsuresFrom.ifOk_iff _ _ _).2 ?_
  rintro db ⟨site⟩ env _complete
  rw [purge_script]
  refine Sql.ifOk_send_plainDelete (table := ⟨site.table, db.raw.rows.getD site.position []⟩)
    site.purgeResolves (Database.table_of_findTable db.raw _ site.position site.table site.found)
    (RunStep.continues_iff.1 (site.purgeModeled env)) ?_
  intro value outputs final reached _valid _allOk
  show Holds.reachedSince (purgeKeeps c now) db final (by check_two_state_query)
  unfold Holds.reachedSince Holds.inContextSince ExecutionContext.defaultObservation
  rw [reached] at *
  exact purge_keeps_rows site _ rfl

#print axioms purge_keeps_rows
#print axioms purge_frame

end AssertionExamples
