import PurgeFrameSite

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the guide's purge frame claim as a fresh-run
triple over every admitted database (ADR 0017, S6). For every pair of values, also NULL and text, a purge that
succeeds leaves every session of the start that is not an expired session of the customer, when the schema and the
resolution of the purge and of the claim are as the fields of `PurgeFrameSite` say. The claim compares the reached
database with the captured start through the schema `before`, and uses the NULL-aware condition `IS NOT 1`. -/

set_option doc.verso true

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- For every database with the site of the purge, values, and reached database that holds the rows that the delete of
the purge keeps, the two-state observation of the claim over the start and the reached database has rows. In plain
words: every row of the start for which the condition is not 1 is still in the reached table. Proof sketch: the claim
resolves against the catalog of the start and the reached catalog, which the delete does not change
({name}`PurgeFrameSite.claimResolves`), so {name}`Script.observeTwoStateIn_resolved` gives the output of the resolved
statement with the start. The laws of the parts then apply in turn: {lit}`SELECT 1 WHERE`
({name}`resolvedStepOutput_selectOneWhere_hasRows`), {lit}`NOT EXISTS` ({name}`Resolved.Expr.truthy_notExists`), the
subqueries of the statement ({name}`Resolved.statementContext_subqueries`, {name}`Resolved.subqueryContext_subqueries`),
the {lit}`EXCEPT` compound ({name}`Resolved.Query.PlainExcept.subqueryRun`) and the read of each table
({name}`Resolved.Query.simple_subqueryRun`). The compound is empty when each row of its first term is a row of the
second ({name}`CompoundOperator.except_combine_eq_nil`): a row with a condition that is not 1 is not selected by the
filter ({name}`Resolved.Expr.truthy_isNot_one`), so the delete keeps it ({name}`LiteralData.mem_deleted`). The first
cell of a row is its rowid, so the rows of the first term are identical where they compare equal
({name}`Resolved.equalRowsIdentical_rowidFirst`). -/
theorem purge_keeps_rows {db : Database} {c now : Value} (site : PurgeFrameSite db)
    (deleteContext : Resolved.EvalContext) (parameters : deleteContext.parameters = [c, now]) :
    ((purgeKeeps c now).observeTwoStateIn db.raw
      (Database.Raw.observationContext (db.raw.setRows site.position
        (LiteralData.deleted deleteContext ⟨site.table, db.raw.rows.getD site.position []⟩ (some purgeFilter)).rows))).hasRows =
      true := by
  have present := Database.table_of_findTable db.raw _ site.position site.table site.found
  have aligned := Model.Database.position_lt_rows db.valid.admitted.rowsShaped site.found
  have admitted := db.valid.admitted.table present
  generalize keptDef : LiteralData.deleted deleteContext ⟨site.table, db.raw.rows.getD site.position []⟩
    (some purgeFilter) = kept
  have current := Model.Database.table_setRows kept.rows present aligned
  have initialQuiet := Resolved.Query.simple_expressions_rowwise
    [{ kind := .inner, source := .initialTable site.position, condition := none }] (some purgeKeepsCondition)
    sessionColumns site.names (by simp [Resolved.QuerySource.expressions]) (by simpa using purgeKeepsCondition_rowwise)
    sessionColumns_rowwise
  have currentQuiet := Resolved.Query.simple_expressions_rowwise [.first site.position] none sessionColumns site.names
    (by simp [Resolved.QuerySource.first, Resolved.QuerySource.expressions]) (by simp) sessionColumns_rowwise
  have initialRead := fun context database => Resolved.Query.simple_subqueryRun context database [] (some db.raw)
    _ (some purgeKeepsCondition) sessionColumns site.names
    (Resolved.Query.source_initialTable _ (purgeKeepsInitialTerm site.position site.names) _ _ _ _ rfl present) rfl rfl
    (fun row _ expression member => (initialQuiet expression member).fault_none context row)
  have currentRead := fun context => Resolved.Query.simple_subqueryRun context _ [] (some db.raw) _ none sessionColumns
    site.names (Resolved.Query.source_first_from _ (purgeKeepsCurrentTerm site.position site.names) _ _ _ _ rfl current)
    rfl rfl (fun row _ expression member => (currentQuiet expression member).fault_none context row)
  have subset : ∀ context : Resolved.EvalContext, context.parameters = [c, now] →
      ∀ output ∈ ((Resolved.sourceRows ⟨site.table, db.raw.rows.getD site.position []⟩).filter fun cells =>
          (some purgeKeepsCondition).all fun condition => Resolved.truthy (condition.eval context cells)).map
          (fun cells => sessionColumns.map (·.eval context cells)),
        output ∈ ((Resolved.sourceRows ⟨site.table, kept.rows⟩).filter fun cells =>
          (none : Option Resolved.Expr).all fun condition => Resolved.truthy (condition.eval context cells)).map
          (fun cells => sessionColumns.map (·.eval context cells)) := by
    intro context bound output member
    simp only [List.mem_map, List.mem_filter, Option.all_some, Option.all_none, and_true] at member ⊢
    obtain ⟨cells, ⟨scanned, keep⟩, rfl⟩ := member
    refine ⟨cells, ?_, rfl⟩
    obtain ⟨row, inside, rfl⟩ := (mem_sourceRows_iff _ cells).1 scanned
    refine (mem_sourceRows_iff _ _).2 ⟨row, ?_, rfl⟩
    rw [← keptDef, LiteralData.mem_deleted]
    refine ⟨inside, ?_⟩
    rw [purgeKeepsCondition, Resolved.Expr.truthy_isNot_one rfl, Bool.not_eq_true'] at keep
    simp only [LiteralData.selected, Option.all_some, Resolved.Expr.eval]
    rw [purgeFilter_rowwise.evaluate_congr deleteContext context row.values (by rw [parameters, bound])]
    exact keep
  have compound : ∀ counters, ((purgeKeepsCompound site.names).subqueryRun
      (Resolved.subqueryContext 0 counters [c, now] (db.raw.setRows site.position kept.rows)
        [purgeKeepsCompound site.names, purgeKeepsInitialTerm site.position site.names,
          purgeKeepsCurrentTerm site.position site.names] (some db.raw) 2)
      (db.raw.setRows site.position kept.rows) [] (some db.raw)).rows = [] ∧
      ((purgeKeepsCompound site.names).subqueryRun
      (Resolved.subqueryContext 0 counters [c, now] (db.raw.setRows site.position kept.rows)
        [purgeKeepsCompound site.names, purgeKeepsInitialTerm site.position site.names,
          purgeKeepsCurrentTerm site.position site.names] (some db.raw) 2)
      (db.raw.setRows site.position kept.rows) [] (some db.raw)).fault = .none := by
    intro counters
    have left := Resolved.subqueryContext_subqueries 0 counters [c, now] (db.raw.setRows site.position kept.rows)
      [purgeKeepsCompound site.names, purgeKeepsInitialTerm site.position site.names,
        purgeKeepsCurrentTerm site.position site.names] (some db.raw) 1 1 [] rfl
    have right := Resolved.subqueryContext_subqueries 0 counters [c, now] (db.raw.setRows site.position kept.rows)
      [purgeKeepsCompound site.names, purgeKeepsInitialTerm site.position site.names,
        purgeKeepsCurrentTerm site.position site.names] (some db.raw) 1 2 [] rfl
    have leftRead := initialRead (Resolved.subqueryContext 0 counters [c, now]
      (db.raw.setRows site.position kept.rows) [purgeKeepsCompound site.names,
        purgeKeepsInitialTerm site.position site.names, purgeKeepsCurrentTerm site.position site.names]
      (some db.raw) 1) (db.raw.setRows site.position kept.rows)
    have rightRead := currentRead (Resolved.subqueryContext 0 counters [c, now]
      (db.raw.setRows site.position kept.rows) [purgeKeepsCompound site.names,
        purgeKeepsInitialTerm site.position site.names, purgeKeepsCurrentTerm site.position site.names]
      (some db.raw) 1)
    have final := (purgeKeepsCompound_shape site.names).subqueryRun _ (db.raw.setRows site.position kept.rows)
      (some db.raw) (by rw [left]; exact leftRead.2.2) (by rw [right]; exact rightRead.2.2) (by
        rw [left]
        erw [leftRead.1]
        exact Resolved.equalRowsIdentical_rowidFirst admitted.rowidsDistinct admitted.rowsAliased site.keyAlias
          .binary [.binary, .binary] _ [.column 1, .column 2] fun cells member => (List.mem_filter.1 member).1)
    refine ⟨?_, final.2⟩
    rw [final.1, left, right]
    erw [leftRead.1, rightRead.1]
    exact CompoundOperator.except_combine_eq_nil _ _ _ (subset _ rfl)
  have resolves : resolveTwoState runContext db.raw.catalog
      (Database.Raw.observationContext (db.raw.setRows site.position kept.rows)).connection.state.database.catalog
      purgeKeepsParts.1 purgeKeepsParts.2 = .ok (purgeKeepsResolved site.position site.names, site.claimAfter) :=
    site.claimResolves
  rw [Script.observeTwoStateIn_resolved (script := purgeKeeps c now) (statement := purgeKeepsStatement)
    (parameters := [c, now]) (query := purgeKeepsParts.1) (subqueries := purgeKeepsParts.2) db.raw _ rfl
    purgeKeepsStatement_asQuery resolves]
  simp only [purgeKeeps_usesSchema, ↓reduceIte]
  refine (resolvedStepOutput_selectOneWhere_hasRows _ _ _ _ _ _ _ (purgeKeepsResolved_calm site.position site.names)
    ?_).2 ?_
  · rw [Resolved.Expr.fault_not, Resolved.Expr.fault_exists, Resolved.statementContext_subqueries _ _ _ _ _ _ _ _ rfl]
    exact (compound _).2
  rw [Resolved.Expr.truthy_notExists, Resolved.statementContext_subqueries _ _ _ _ _ _ _ _ rfl]
  exact List.isEmpty_iff.2 (compound _).1

/-- The guide's frame claim of the purge, for every pair of values: for every admitted database with the site of the
purge and every complete environment, every run of the purge from the fresh start that has no error ends in a database
in which every session of the start that is not an expired session of the customer is still there. The values may be
NULL or text. The claim reads the start through {lit}`before` and states the unchanged rows with the condition
{lit}`IS NOT 1`, so a NULL parameter does not weaken it. A purge that fails requires nothing, and the model's rollback
decides what a failed run leaves. Proof sketch: the check of the one statement; the step of the purge continues
({name}`PurgeFrameSite.purge_continues`), the plain delete stores the rows that {name}`LiteralData.deleted` keeps
({name}`runScriptStep_plainDelete_eq`), and {name}`purge_keeps_rows` shows that the observation of the claim over the
start and that database has rows. -/
theorem purge_frame (c now : Value) :
    FreshEnsuresFrom (send (purge c now)) (fun db => Nonempty (PurgeFrameSite db))
      (fun start => ifOk (holdsSince start (purgeKeeps c now))) := by
  refine (FreshEnsuresFrom.ifOk_iff _ _ _).2 ?_
  rintro db ⟨site⟩ env _complete
  rw [purge_script]
  have present := Database.table_of_findTable db.raw _ site.position site.table site.found
  sql_run [site.purgeResolves, site.purge_continues env c now, present]
  intro _allOk
  exact purge_keeps_rows site _ rfl


#print axioms purge_keeps_rows
#print axioms purge_frame

end AssertionExamples
