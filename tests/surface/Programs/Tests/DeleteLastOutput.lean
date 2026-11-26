import DeleteReadComparison

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

namespace DeleteLastOutput
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open scoped Belay.Sqlite.LastOutput
open SelectContextCases (bigScript deleteScript bigAt)
open SelectJoinCases (shop ordersShape)
open DeleteReadComparison (referenceScript expected returnsBag reference_at big_start delete_effect)

/-- A calm SELECT on the shop catalog that scans only orders returns a normalized row list
when it has no compound, ordering, limit or offset, evaluation succeeds and distinctness
is certain for all inputs. Proof sketch: transfer the resolution to the current connection
and apply {name}`resolvedStepOutput_calm_unordered` to the table at the resolved position. -/
private theorem normalizedStep {state : ExecutionContext} {stmt : Syntax.Statement}
    (schema : state.HasCatalog shop) (sel : stmt.asQuery?.isSome = true) {q : Resolved.Query}
    (resolved : resolveStatement runContext (shop.raw.connection {}).resolveState stmt =
      .ok (.query q [], (shop.raw.connection {}).resolveState))
    (sources : q.sources = [.first 1]) (calm : (Resolved.Statement.query q []).Calm)
    (single : q.compound = none) (lp : q.limitParameter = none) (op : q.offsetParameter = none)
    (unordered : q.orderBy = []) (offset : q.offset = 0) (lim : q.limit = none)
    (nofail : ∀ rows, q.fails (Resolved.EvalContext.bound []) rows = false)
    (certain : ∀ rows, q.distinctCertain (Resolved.EvalContext.bound []) rows = true) :
    ∃ rows, (runScriptStep runContext state.clock state.index state.connection stmt []).output =
      .rows (Resolved.normalForm rows) := by
  have present : state.connection.state.database.table 1 =
      some ⟨ordersShape, state.connection.state.database.rows.getD 1 []⟩ := by
    simp [Model.Database.table, show state.connection.state.database.catalog = shop.raw.catalog from schema,
      show shop.raw.catalog.tableAt 1 = some ordersShape from rfl]
  have eq := select_resolution_of_same_catalog runContext stmt sel state.connection.resolveState
    (shop.raw.connection {}).resolveState schema
  rw [resolved] at eq
  cases h : resolveStatement runContext state.connection.resolveState stmt with
  | error e => simp [h, Except.map] at eq
  | ok pair =>
    rcases pair with ⟨st, after⟩
    simp [h, Except.map] at eq
    subst st
    rw [runScriptStep_output_of_resolved h]
    refine ⟨_, resolvedStepOutput_calm_unordered _ _ _ _ calm single lp op unordered offset lim
      (Resolved.Query.source_first _ q _ 1 _ sources present) (by intro impossible; cases impossible) (nofail _) (certain _)⟩

/-- Read the statement from a singleton script to apply the step laws. -/
private def firstStmt (s : Script) (one : s.statements.length = 1) := (s.statements[0]'(by omega)).1

/-- Discharge the scan premises shared by the two concrete queries. -/
local macro "norm_select" schema:term : tactic =>
  `(tactic| (apply normalizedStep $schema rfl (by rfl) rfl (by decide +kernel) rfl rfl rfl rfl rfl rfl
                 (by intro rows; simp [Resolved.Query.fails]) (by intro rows; rfl)))

/-- The reference scan returns normalized rows at any context with the shop catalog. -/
private theorem refNorm (state : ExecutionContext) (schema : state.HasCatalog shop) :
    ∃ rows, (runScriptStep runContext state.clock state.index state.connection (firstStmt referenceScript rfl) []).output
      = .rows (Resolved.normalForm rows) := by norm_select schema

/-- The big-orders scan returns normalized rows at any context with the shop catalog. -/
private theorem bigNorm (state : ExecutionContext) (schema : state.HasCatalog shop) :
    ∃ rows, (runScriptStep runContext state.clock state.index state.connection (firstStmt bigScript rfl) []).output
      = .rows (Resolved.normalForm rows) := by norm_select schema

/-- For a singleton SELECT with empty parameters, if its step returns normalized rows
and its query returns the given bag, its send ends with that normalized bag.
Proof sketch: the query check identifies the bag of the step. The SELECT send rule
then gives that output at the end of each branch. -/
private theorem endsRows (s : Script) (one : s.statements.length = 1)
    (sel : (firstStmt s one).asQuery?.isSome = true)
    (head : s.statements = [(firstStmt s one, [])])
    (state : ExecutionContext) (bag : List (List Value))
    (norm : ∃ rows, (runScriptStep runContext state.clock state.index state.connection (firstStmt s one) []).output =
      .rows (Resolved.normalForm rows))
    (checked : (query s one).check (fun result _ => returnsBag bag result) state) :
    (send s).check (fun _ final => final.outputs.getLast? = some (.rows (Resolved.normalForm bag))) state := by
  let stmt := firstStmt s one
  have head' : s.statements = [(stmt, [])] := head
  have select : s.isSelect = true := by simpa [Script.isSelect, head'] using sel
  have checked' := (check_query_returnsResult_iff (one := one) select (fun rows => rows.Perm bag) state).mp checked
  have args : (s.statements[0]'(by omega)).2 = [] := by simp [head']
  rw [args] at checked'
  obtain ⟨rows, output⟩ := norm
  change (runScriptStep runContext state.clock state.index state.connection stmt []).output.returnsResult _ at checked'
  rw [output] at checked'
  have same := (Resolved.normalForm_eq_iff_perm rows bag).mpr ((Resolved.normalForm_perm rows).symm.trans checked')
  rw [same] at output
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, form⟩ := Syntax.Statement.select_of_asQuery sel
  change stmt = _ at form
  have script : s = ⟨[(stmt, [])]⟩ := by rw [← head']
  rw [script]
  apply Sql.check_send_select form
  · cases step : runScriptStep runContext state.clock state.index state.connection stmt [] with
    | ended => rw [step] at output; cases output
    | continued => exact ⟨_, _, _, rfl⟩
  · intro selected choice
    rw [output] at choice
    obtain rfl | impossible := choice
    · simp [ExecutionContext.next]
    · exact impossible.elim

/-- For every shop database and complete environment, deleting orders without a customer
and then reading big orders has the same last output as filtering for both conditions
in the original database. Proof sketch: identify the surviving rows with the reference
query's rows and use the common normalized output on every branch. -/
theorem delete_last : deleteScript; bigScript ~ referenceScript on shop := by
  intro db schema env _
  let s := ExecutionContext.initial db env
  apply Script.lastOutputProfile_eq_of_check _ _ db env (.rows (Resolved.normalForm (expected db.raw)))
  · apply (check_send_append _ _ _ _).2
    apply Sql.check_mono (delete_effect db env schema)
    intro _ final ⟨catalog, perm⟩
    have after := endsRows bigScript rfl rfl rfl final _ (bigNorm final catalog) (big_start final catalog)
    simpa only [(Resolved.normalForm_eq_iff_perm _ _).mpr perm] using after
  · exact endsRows referenceScript rfl rfl rfl s _ (refNorm s schema) (reference_at s schema)

#print axioms delete_last

/-- An overflowing ABS records an error before execution continues. -/
private def overflow := sql r"SELECT abs(-9223372036854775808)"

/-- A final query with a fixed output after the earlier error. -/
private def seven := sql r"SELECT 7"

example : (shop.run (send (overflow ++ seven))).outputs = [.error 1, .rows [[.integer 7]]] := by decide +kernel

example : overflow; seven ~ seven on shop := by
  intro db schema env complete
  apply observationProfile_of_singletons
  · exact fun run => Sql.branch_iff_actual _ _ _ _ run (by rfl)
  · exact fun run => Sql.branch_iff_actual _ _ _ _ run (by rfl)
  · rfl

example : ¬ (seven; overflow ~ seven on shop) := by
  intro same
  let env : Env := { Env.newConnection with clock := some fun _ => 0 }
  have actual := observationProfile_actual (same shop rfl env ⟨rfl, rfl, rfl, rfl⟩)
  change some (Output.error 1) = some (.rows [[.integer 7]]) at actual
  cases actual

example : (referenceScript ~ deleteScript; bigScript on shop) := by
  intro db schema env complete
  exact (delete_last db schema env complete).symm

end DeleteLastOutput
