import SelectDerivedSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance cases A21 and A22 of ADR 0027, through the context rules of a SELECT
({lit}`check_query_select_at`, {lit}`check_query_select_faultless`): a SELECT after a write reads
the database of the context that the write reached, and a SELECT of {lit}`changes()` reads the
counters of the context, under an explicit premise about them. Both rules give that the SELECT
keeps the connection. -/

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
the counters of the context can be any. Proof sketch: {name}`check_query_select_faultless` over
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
  refine check_query_select_faultless rfl head state (by rw [shape]; exact resolves)
    (by unfold Resolved.Statement.Calm; decide +kernel) rfl (Resolved.Query.source_first _ bigQuery _ 1 _ rfl present)
    (by simp) (Resolved.Query.bindWindow_literal _ _ rfl rfl)
    (fun row _ expression member => by
      simp [bigQuery, Resolved.Query.expressions, Resolved.Query.keptExpressions,
        Resolved.QuerySource.expressions, Resolved.QuerySource.first, Resolved.Output.scalars, Resolved.Output.operands] at member
      rcases member with rfl | rfl | rfl <;> rfl)
    (by simp [Resolved.Query.fails, bigQuery]) (by simp [Resolved.Query.distinctCertain, bigQuery]) _ ?_
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
{name}`Sql.check_query_ofResolveState` with the resolution state of the context and closes the result
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
sketch: {name}`Sql.check_send_plainDelete`; a write keeps the catalog, so each reached context
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
  refine Sql.check_send_plainDelete (ExecutionContext.initial_holds_valid db env)
    (by show resolveStatement runContext (db.raw.connection env.counters).resolveState statement = _
        rw [shop_state db env schema]; exact resolves)
    (Database.table_of_findTable db.raw _ 1 ordersShape (shop_found db schema).2)
    (modeled (statement, []) (by rw [head]; exact List.mem_singleton_self _)) ?_ ?_
  · intro output value next _ _ _ same _
    subst same
    exact (Connection.resolveState_afterWrite _ _ (by rfl)).trans (shop_state db env schema)
  · intro output value next _ _ same _
    subst same
    exact (Connection.resolveState_afterWrite _ _ (by rfl)).trans (shop_state db env schema)

/-- A21 contrast on {name}`partial_`, with the rows of native SQLite 3.51.0: from the start,
{name}`bigScript` returns the orders 1 and 3; after {name}`deleteScript`, which deletes order 3,
it returns order 1 alone, so the result from the start does not hold after the write. -/
example : (partial_.run (query bigScript rfl)).returnsResult
      (·.Perm [[.integer 1, .integer 10], [.null, .integer 7]]) ∧
    (partial_.run (do let _ ← send deleteScript; query bigScript rfl)).outputs =
      [.done 1, .rows [[.integer 1, .integer 10]]] := by
  decide +kernel

/-- The A22 query, which reads the counter of {lit}`changes()`. -/
def changesScript : Script := sql r"SELECT changes()"

/-- The query {lit}`SELECT changes()`, without a source. -/
def changesQuery : Resolved.Query := Resolved.Query.simple [] none [.scalar (.counter .changes)] ["changes()"]

/-- A22: for every context whose counters give {lit}`changes()` the value {lit}`count`, the
program {name}`query` of {name}`changesScript` checks that the result is the one row
{lit}`count` and that the reached context has the connection of the start. The clock, the index
and the database of the context can be any. Proof sketch: {name}`check_query_select_at` with the
readiness of {name}`Connection.SelectReady.of_phases`, whose counter premise is the premise
{lit}`known`. -/
theorem changes_at (state : ExecutionContext) (count : Nat) (known : state.connection.state.counters.changes = some count) :
    (query changesScript rfl).check
      (fun result final => result = .ok [[.integer count]] ∧ final.connection = state.connection) state := by
  have resolved := resolveStatement_selectNoFrom_columns runContext state.connection.resolveState
    (.call "changes" []) "changes()" "changes()" none (.counter .changes) none none
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (FilterResolves.of_none _ _ _ _)
  rw [show Resolved.Query.simple [] none [.scalar (.counter .changes)] ["changes()"] = changesQuery from rfl] at resolved
  have reads : (Resolved.Statement.query changesQuery []).counterReads = [.changes] := by decide +kernel
  refine check_query_select_at rfl rfl state resolved (value := 0) rfl
    (Connection.SelectReady.of_phases rfl (by rw [reads]; simp [Counters.firstUnknown, Counters.read, known])
      (Resolved.Query.source_none _ _ _ rfl) rfl (by simp) (Resolved.Query.bindWindow_literal _ _ rfl rfl)
      (by simp [Resolved.Query.fails, changesQuery, Resolved.Query.simple])
      (Resolved.Query.mustFail_of_faultless _ _ _ fun _ _ expression member => by
        simp [changesQuery, Resolved.Query.simple, Resolved.Query.expressions, Resolved.Query.keptExpressions,
          Resolved.Output.scalars, Resolved.Output.operands] at member
        subst member; rfl)
      (Resolved.Query.mayFail_of_faultless _ _ _ (by decide +kernel) fun _ _ expression member => by
        simp [changesQuery, Resolved.Query.simple, Resolved.Query.expressions, Resolved.Query.keptExpressions,
          Resolved.Output.scalars, Resolved.Output.operands] at member
        subst member; rfl)
      (by simp [Resolved.Query.distinctCertain, changesQuery, Resolved.Query.simple])) _ ?_
  intro result member final same
  have perm := Resolved.Query.perm_of_mem_possibleResults_plain rfl rfl rfl rfl rfl member
  rw [Resolved.filtered_of_filter_none _ rfl] at perm
  refine ⟨?_, same⟩
  rw [List.perm_singleton.mp perm]
  simp only [Connection.queryContextAt, reads]
  simp [Resolved.Query.rowOutput, changesQuery, Resolved.Query.simple, Counters.view, Counters.read, known,
    Resolved.Expr.eval, Resolved.Expr.evaluate]

/-- A22 contrast on {name}`shop` and {name}`partial_`, with the rows of native SQLite 3.51.0:
with the default environment, which knows no counter, {name}`changesScript` alone gives no
result; with the counters of a new connection it gives 0; after {name}`deleteScript`, which
deletes one row, it gives 1 also with the default environment, because the write sets the
counter of the reached context. -/
example : ¬ (shop.run (query changesScript rfl)).returnsResult (fun _ => True) ∧
    (shop.run (query changesScript rfl) Env.newConnection).returnsResult (· = [[.integer 0]]) ∧
    (partial_.run (do let _ ← send deleteScript; query changesScript rfl)).outputs =
      [.done 1, .rows [[.integer 1]]] := by
  decide +kernel

#print axioms big_at
#print axioms big_after
#print axioms big_after_delete
#print axioms changes_at

end SelectContextCases
