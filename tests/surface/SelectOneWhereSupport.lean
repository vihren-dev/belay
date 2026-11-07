import Belay

set_option doc.verso true

/-! Support of the claims about {lit}`SELECT 1 WHERE c` with one subquery over every database, through
the phase rules of ADR 0027: the faultless execution rule ({lit}`Run.query_returnsResult_faultless`),
the source rule of a query without a table ({lit}`Resolved.Query.source_none`), the plain existence
and emptiness rules, and the subquery run rule ({lit}`Resolved.Query.subqueryRun_of_faultless`). The
fixtures {lit}`ClaimsExists` and {lit}`CustomerInsertQueries` use it. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The subquery {lit}`SELECT 1 FROM t WHERE p` of the table at a position. -/
abbrev tableOne (position : Nat) (condition : Option Resolved.Expr) : Resolved.Query :=
  Resolved.Query.simple [.first position] condition [.scalar (.literal (.integer 1))] ["1"]

/-- Whether the condition {lit}`p`, if any, is true with the values for some source row of the table at a
position. -/
def someRow (db : Database) (parameters : List Value) (position : Nat) (table : CatalogTable)
    (condition : Option Resolved.Expr) : Bool :=
  (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }).any fun row =>
    condition.all fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)

/-- For every database with a table at a position under some name, values and calm condition {lit}`p`:
the run of {name}`tableOne` as a subquery with the values for the row with no cells has no fault,
and has no rows exactly when {name}`someRow` is false. Proof sketch:
{name}`Resolved.Query.subqueryRun_of_faultless` with the scan of the table
({name}`Resolved.Query.sourceAfter_first`), then
{name}`Resolved.Query.results_eq_nil_iff_plain`. -/
theorem tableOne_run (db : Database) (parameters : List Value) (name : Identifier) (position : Nat)
    (table : CatalogTable) (condition : Option Resolved.Expr)
    (found : db.raw.catalog.findTable name = some (position, table))
    (calm : ∀ expression ∈ condition.toList, expression.Calm) :
    ((tableOne position condition).subqueryRun (Resolved.EvalContext.bound parameters) db.raw []).fault = .none ∧
      ((tableOne position condition).subqueryRun (Resolved.EvalContext.bound parameters) db.raw []).rows.isEmpty =
        !someRow db parameters position table condition := by
  have plain := (Resolved.Statement.Calm.selectOne_subquery position _ condition (Resolved.Expr.calm_exists 0)
    calm).subquery_plain (List.mem_singleton_self _)
  have run := Resolved.Query.subqueryRun_of_faultless (Resolved.EvalContext.bound parameters) db.raw [] none
    rfl rfl rfl
    (Resolved.Query.sourceAfter_first _ db.raw none _ position _ [] rfl
      (Database.table_of_findTable db.raw _ position table found)) rfl plain
    (fun row _ expression member => Resolved.Expr.fault_of_plain _ (Resolved.EvalContext.bound_quiet parameters)
      row expression (by simpa using List.all_eq_true.mp plain expression member))
    (by simp [Resolved.Query.fails, Resolved.Query.simple])
    (by simp [Resolved.Query.distinctCertain, Resolved.Query.simple])
  rw [run]
  refine ⟨rfl, Bool.eq_iff_iff.mpr ?_⟩
  rw [List.isEmpty_iff, Resolved.Query.results_eq_nil_iff_plain _ rfl rfl rfl rfl (by simp [Resolved.Query.simple])]
  simp [Resolved.filtered, someRow, Resolved.outerCells, List.filter_eq_nil_iff, Resolved.Query.simple]

/-- For every script of one statement with values, database, condition {lit}`c` and subquery:
when the statement resolves to {lit}`SELECT 1 WHERE c` with the one subquery, the statement is calm,
and {lit}`c` has no fault over the row with no cells in the statement context of the values, then

* {name}`Holds` holds exactly when {lit}`c` is true over that row,
* {name (full := Belay.Sqlite.Empty)}`Empty` holds exactly when {lit}`c` is not true over that row, and
* {name}`Fails` does not hold.

Proof sketch: {name}`Run.query_returnsResult_faultless` with {name}`Resolved.Query.source_none`, then
{name}`Resolved.Query.forall_possibleResults_ne_nil_plain` and
{name}`Resolved.Query.forall_possibleResults_eq_nil_plain`. -/
theorem whereOne_claims {script : Script} {isQuery : script.isQuery = true} (statement : Syntax.Statement)
    (parameters : List Value) (head : script.statements = [(statement, parameters)]) (db : Database)
    (main : Resolved.Expr) (inner : Resolved.Query)
    (resolved : resolveStatement runContext (db.raw.connection Env.default.counters).resolveState statement =
      .ok (.query (Resolved.Query.selectOneWhere main) [inner], (db.raw.connection Env.default.counters).resolveState))
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere main) [inner]).Calm)
    (quiet : (main.evaluate (Resolved.EvalContext.statement parameters db.raw [inner]) []).2 = .none) :
    (Holds script db isQuery ↔
        Resolved.truthy (main.eval (Resolved.EvalContext.statement parameters db.raw [inner]) []) = true) ∧
      (Empty script db isQuery ↔
        Resolved.truthy (main.eval (Resolved.EvalContext.statement parameters db.raw [inner]) []) = false) ∧
      ¬ Fails script db isQuery := by
  have one : script.statements.length = 1 := by simp [head]
  have rule := fun property => (Run.send_returnsResult_iff_query one db Env.default property).trans
    (Run.query_returnsResult_faultless head one db Env.default resolved (Resolved.Query.source_none _ _ _ rfl) (by simp)
      calm rfl (Resolved.Query.bindWindow_literal _ _ rfl rfl)
      (fun row member expression inside => by
        have empty : row = [] := by simpa using member
        subst empty
        exact Resolved.Query.selectOneWhere_faultless _ main quiet expression inside)
      (by simp [Resolved.Query.fails, Resolved.Query.simple])
      (by simp [Resolved.Query.distinctCertain, Resolved.Query.simple]) property)
  have holds : Holds script db isQuery ↔
      Resolved.truthy (main.eval (Resolved.EvalContext.statement parameters db.raw [inner]) []) = true :=
    (rule _).trans ((Resolved.Query.forall_possibleResults_ne_nil_plain rfl rfl rfl rfl rfl).trans
      (by simp [Resolved.Query.simple]))
  have empty : Belay.Sqlite.Empty script db isQuery ↔
      Resolved.truthy (main.eval (Resolved.EvalContext.statement parameters db.raw [inner]) []) = false :=
    (rule _).trans ((Resolved.Query.forall_possibleResults_eq_nil_plain rfl rfl rfl rfl rfl).trans
      (by simp [Resolved.Query.simple]))
  refine ⟨holds, empty, ?_⟩
  cases truth : Resolved.truthy (main.eval (Resolved.EvalContext.statement parameters db.raw [inner]) [])
  · exact Empty.not_fails (empty.2 truth)
  · exact Holds.not_fails (holds.2 truth)

#print axioms tableOne_run
#print axioms whereOne_claims
