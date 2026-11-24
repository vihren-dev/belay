import SelectDerivedSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! ADR 0027 case A21 uses {name}`Belay.Sqlite.Sql.check_query_of_step_rows` to read orders at
the connection reached by a write. -/

namespace SelectContextCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)
open SelectJoinCases (shop ordersShape shop_found shop_state partial_)
open SelectDerivedCases (bigCondition bigQuery Big)

/-- The A21 query, which resolves to {name}`bigQuery`. -/
def bigScript : Script := sql r"SELECT customer_id, amount FROM orders WHERE amount > 5"

/-- The specification of {name}`bigQuery` over a database of the model: the {lit}`customer_id`
and the {lit}`amount` of each {name}`Big` row of {lit}`orders` at position 1, in scan order. -/
def bigAt (database : Model.Database) : List (List Value) :=
  ((Resolved.sourceRows { shape := ordersShape, rows := database.rows.getD 1 [] }).filter Big).map
    fun order => [cell 1 order, cell 2 order]

/-- The A21 post of a result and a reached context: the result is successful and a permutation
of {name}`bigAt` of the database of the reached context. An error does not satisfy it. -/
def ReadsBig (result : Except Nat (List (List Value))) (final : ExecutionContext) : Prop :=
  match result with
  | .ok rows => rows.Perm (bigAt final.connection.state.database)
  | .error _ => False

/-- A21 at a context: for every context whose connection has the resolution state of
{name}`shop` (the catalog of {name}`shop`, no open transaction, and foreign keys and recursive
triggers off), the program {name}`query` of {name}`bigScript` checks {name}`ReadsBig`: it
returns a permutation of {name}`bigAt` of the database of that context. The clock, the index and
the counters of the context can be any. Proof sketch: {name}`Sql.check_query_of_step_rows` over
the scan of {lit}`orders` in the database of the context; the result is a permutation of the
output of the kept rows ({name}`Resolved.Query.perm_of_mem_possibleResults_plain`). -/
theorem big_at (state : ExecutionContext)
    (shape : state.connection.resolveState = (shop.raw.connection {}).resolveState) :
    (query bigScript rfl).check ReadsBig state := by
  obtain ⟨statement, head, resolves⟩ : ∃ statement, bigScript.statements = [(statement, [])] ∧
      resolveStatement runContext (shop.raw.connection {}).resolveState statement =
        .ok (.query bigQuery [], (shop.raw.connection {}).resolveState) := ⟨_, rfl, by decide +kernel⟩
  have catalog : state.connection.state.database.catalog = shop.raw.catalog := congrArg ResolveState.catalog shape
  have present := Database.table_of_findTable state.connection.state.database (name! "orders") 1 ordersShape
    (by rw [catalog]; decide +kernel)
  have calm : (Resolved.Statement.query bigQuery []).Calm := by unfold Resolved.Statement.Calm; decide +kernel
  have resolution : resolveStatement runContext state.connection.resolveState statement =
      .ok (.query bigQuery [], (shop.raw.connection {}).resolveState) := by rw [shape]; exact resolves
  have ready := Connection.SelectReady.of_faultless state.connection [] calm rfl
    (Resolved.Query.bindWindow_literal _ _ rfl rfl) (Resolved.Query.source_first _ bigQuery _ 1 _ rfl present)
    (by simp) (fun row _ expression member => by
      simp [bigQuery, Resolved.Query.expressions, Resolved.Query.keptExpressions,
        Resolved.QuerySource.expressions, Resolved.QuerySource.first, Resolved.Output.scalars, Resolved.Output.operands] at member
      rcases member with rfl | rfl | rfl <;> rfl)
    (by simp [Resolved.Query.fails, bigQuery]) (by simp [Resolved.Query.distinctCertain, bigQuery])
  refine Sql.check_query_of_step_rows rfl head state (property := (· ∈ bigQuery.possibleResults
    (Resolved.EvalContext.statement [] state.connection.state.database []) (Resolved.sourceRows
      {shape := ordersShape, rows := state.connection.state.database.rows.getD 1 []}))) ?_ ?_
  · simp only [runScriptStep_output, resolution]
    rw [resolvedStepOutput_select state.clock state.index _ [] (by simp [statementClock, calm.readsClock]) ready,
      show state.connection.queryContextAt 0 [] bigQuery [] = _ from Connection.queryContext_calm _ _ _ _ calm]
    exact (bigQuery.returnsResult_possible _ _ _).2 fun _ member => member
  intro result member final same
  have perm := Resolved.Query.perm_of_mem_possibleResults_plain rfl rfl rfl rfl rfl member
  generalize Resolved.EvalContext.statement [] state.connection.state.database [] = context at perm
  have output : bigQuery.rowOutput context = fun order => [cell 1 order, cell 2 order] := by
    funext order
    simp [Resolved.Query.rowOutput, bigQuery, Resolved.Expr.eval_column]
  have kept : ∀ rows, Resolved.filtered context bigQuery rows = rows.filter Big := fun rows => by
    simp only [Resolved.filtered, bigQuery]
    rfl
  rw [output, kept] at perm
  show result.Perm (bigAt final.connection.state.database)
  rw [same]
  exact perm

/-- {name}`Big` is the function that gives, for each row, the truth of {name}`bigCondition` on it. The simplifier
unfolds a definition only where it is applied, and {name}`bigAt` uses {name}`Big` as the argument of a
filter; with this hint, {lit}`sql_select` unfolds it there. -/
theorem big_eq : Big = fun order => Resolved.truthy (bigCondition.eval (Resolved.EvalContext.bound []) order) := rfl

/-- A21 after any program: for every program {lit}`first` and context {lit}`state` such that
{lit}`first` checks at {lit}`state` that each reached context has the resolution state of
{name}`shop`, the program that runs {lit}`first` and then {name}`bigScript` checks
{name}`ReadsBig` at {lit}`state`: the SELECT returns the rows of the database that
{lit}`first` reached, not of the database of {lit}`state`. Proof sketch: {name}`Sql.check_bind`,
then at each reached context the procedure {lit}`sql_select`, which applies
{name}`Sql.check_query_catalog_rows_at` with the resolution state of the context and closes the result
with the hints {name}`bigAt`, {name}`big_eq` and {name}`bigCondition`; {name}`big_at` is the same read
by explicit steps. -/
theorem big_after {α : Type} (first : Sql α) (state : ExecutionContext)
    (reaches : first.check (fun _ final => final.connection.resolveState = (shop.raw.connection {}).resolveState) state) :
    (do let _ ← first; query bigScript rfl).check ReadsBig state := by
  refine (Sql.check_bind _ _ _ _).2 (Sql.check_mono reaches fun _ final shape => ?_)
  sql_select [ReadsBig, bigAt, big_eq, bigCondition]

/-- The A21 write, which deletes the orders without a customer. -/
def deleteScript : Script := sql r"DELETE FROM orders WHERE customer_id IS NULL"

/-- A21, a write and a following SELECT: for every database with the catalog of {name}`shop`
and environment, if the model runs the statement of {name}`deleteScript` on the connection of
the environment to a step that continues, then the program that sends {name}`deleteScript` and
then runs {name}`bigScript` checks {name}`ReadsBig` from the new connection of the environment:
the SELECT returns the rows of the database after the delete, also when the delete fails. Proof
sketch: {name}`runScriptStep_plainDelete_eq`; a write keeps the catalog, so each reached context
has the resolution state of {name}`shop`, and {name}`big_after` applies. -/
theorem big_after_delete (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (modeled : ∀ entry ∈ deleteScript.statements, ∃ output next others,
      runScriptStep runContext env.clock 0 (db.raw.connection env.counters) entry.1 entry.2 =
        .continued output next others) :
    (do let _ ← send deleteScript; query bigScript rfl).check ReadsBig (ExecutionContext.initial db env) := by
  obtain ⟨statement, head, resolves⟩ : ∃ statement, deleteScript.statements = [(statement, [])] ∧
      resolveStatement runContext (shop.raw.connection {}).resolveState statement =
        .ok (.delete 1 (some (.compare .is (some .integer) (.column 1) (.literal .null) .binary)) [] [] none,
          (shop.raw.connection {}).resolveState) := ⟨_, rfl, by decide +kernel⟩
  have script : deleteScript = ⟨[(statement, [])]⟩ := by rw [← head]
  refine big_after _ _ ?_
  rw [script]
  have found := resolves
  rw [← shop_state db env schema] at found
  have present := Database.table_of_findTable db.raw _ 1 ordersShape (shop_found db schema).2
  have covered := RunStep.continues_iff.2 (modeled (statement, []) (by rw [head]; exact List.mem_singleton_self _))
  sql_run [found, covered, present]
  exact (Connection.resolveState_afterWrite _ _ (by rfl)).trans (shop_state db env schema)


/-- A21 contrast on {name}`partial_`, with the rows of native SQLite 3.51.0: from the start,
{name}`bigScript` returns the orders 1 and 3; after {name}`deleteScript`, which deletes order 3,
it returns order 1 alone, so the result from the start does not hold after the write. -/
example : (partial_.run (query bigScript rfl)).returnsResult
      (·.Perm [[.integer 1, .integer 10], [.null, .integer 7]]) ∧
    (partial_.run (do let _ ← send deleteScript; query bigScript rfl)).outputs =
      [.done 1, .rows [[.integer 1, .integer 10]]] := by
  decide +kernel

#print axioms big_at
#print axioms big_after
#print axioms big_after_delete

end SelectContextCases
