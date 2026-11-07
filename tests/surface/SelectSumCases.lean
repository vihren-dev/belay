import Belay

set_option doc.verso true
set_option sql.check false

/-! Acceptance case A09 for {lit}`sum` (ADR 0027): {lit}`SELECT sum(cents) FROM ledger` over every
database whose catalog has a table {lit}`ledger` with a column {lit}`cents`. The run fails with
{lit}`integer overflow` when the integer sum leaves the 64-bit range (the overflow rule of
execution), and otherwise returns one row with the sum, the row of NULL for a table without a row.
Each claim has instances on databases, where {lit}`decide +kernel` checks its premise, so that no
claim is vacuous: two rows of 4611686018427387904, two small rows, no row, and eleven texts that
{lit}`sum` reads as integers. -/

namespace SelectSumCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The A09 query: the sum of the cents of the ledger. -/
def sumCents : Script := sql r"SELECT sum(cents) FROM ledger"

/-- The A09 query has one statement. -/
theorem sumCents_one : sumCents.statements.length = 1 := rfl

/-- The scan of the table at {lit}`position` with the catalog table {lit}`table`. -/
abbrev scanOf (db : Database) (position : Nat) (table : CatalogTable) : List (List Value) :=
  Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }

/-- The sum of the column at {lit}`index`, as the query resolves it. -/
abbrev centsSum (index : Nat) : Resolved.Aggregate := .sum (.column index)

/-- The query to which {name}`sumCents` resolves: the whole-table aggregate of the column. -/
abbrev sumQuery (position index : Nat) : Resolved.Query :=
  Resolved.Query.aggregateOf [.first position] none (centsSum index) "sum(cents)"

/-- For every database whose catalog has a table {lit}`ledger` at {lit}`position` with a column
{lit}`cents` at {lit}`index`, and every environment, the statement of {name}`sumCents` resolves to
{name}`sumQuery` and leaves the state as it is. Proof sketch:
{name}`resolveStatement_select_aggregate` with the column of the table
({name}`resolveOperand_identifier_table`) and no condition. -/
theorem sumCents_resolved (db : Database) (env : Env) {position index : Nat} {table : CatalogTable}
    (found : db.raw.catalog.findTable (name! "ledger") = some (position, table))
    (column : columnPosition table.columns (name! "cents") = some index) :
    resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match sumCents.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query (sumQuery position index) [], (db.raw.connection env.counters).resolveState) :=
  resolveStatement_select_aggregate runContext (db.raw.connection env.counters).resolveState
    { table := name! "ledger", alias := none } none "sum" (.identifier (name! "cents") .none) none "sum(cents)" .sum rfl
    position table (.column index) _ none rfl rfl rfl found (resolveOperand_identifier_table column) rfl (.inl ⟨rfl, rfl⟩)

/-- For every position and index, the statement of {name}`sumQuery` is calm: its one expression is
a column. Proof sketch: {name}`Resolved.Statement.Calm.aggregateOf_first`. -/
theorem sumQuery_calm (position index : Nat) : (Resolved.Statement.query (sumQuery position index) []).Calm :=
  Resolved.Statement.Calm.aggregateOf_first position none _ _ (by simp)
    (by simp [Resolved.Output.operands, Resolved.Expr.calm_column])

/-- For every database whose catalog has a table {lit}`ledger` at {lit}`position` with a column
{lit}`cents` at {lit}`index`, and every environment, the run of {name}`sumCents` returns a result
with a property {lit}`Q` exactly when {lit}`Q` holds of the one row of the sum over the scan of the
table, provided the sum does not fail; the clock and the counters do not matter. Proof sketch:
{name}`resolveStatement_select_aggregate` resolves the query to {name}`sumQuery`, and
{name}`Run.query_returnsResult_calmTable` with {name}`Resolved.Query.aggregateOf_possibleResults`
reads its one result. -/
theorem sumCents_results (db : Database) (env : Env) {position index : Nat} {table : CatalogTable}
    (found : db.raw.catalog.findTable (name! "ledger") = some (position, table))
    (column : columnPosition table.columns (name! "cents") = some index)
    (safe : (centsSum index).fails (Resolved.EvalContext.bound []) (scanOf db position table) = false)
    (property : List (List Value) → Prop) :
    (db.run (query sumCents sumCents_one) env).returnsResult property ↔
      property [[(centsSum index).eval (Resolved.EvalContext.bound []) (scanOf db position table)]] := by
  rw [Run.query_returnsResult_calmTable (script := sumCents) rfl sumCents_one db env (sumCents_resolved db env found column) rfl
    (Database.table_of_findTable _ _ _ _ found) (sumQuery_calm position index) rfl rfl rfl
    (by rw [Resolved.Query.aggregateOf_fails, Resolved.filtered_of_filter_none _ (query := sumQuery position index) rfl]; exact safe) rfl property]
  simp only [Resolved.Query.aggregateOf_possibleResults, Resolved.filtered_of_filter_none _ (query := sumQuery position index) rfl,
    List.mem_singleton, forall_eq]

/-- For every database and environment as in {name}`sumCents_results`, when the sum over the scan
fails, the run of {name}`sumCents` returns no result, and it returns an error with a property
{lit}`E` of the result code exactly when {lit}`E` holds of the code of
{name}`ExecutionError.integerOverflow`. Proof sketch: the resolution of {name}`sumCents_results`
and the overflow rule {name}`Run.query_overflow_calmTable`. -/
theorem sumCents_overflow (db : Database) (env : Env) {position index : Nat} {table : CatalogTable}
    (found : db.raw.catalog.findTable (name! "ledger") = some (position, table))
    (column : columnPosition table.columns (name! "cents") = some index)
    (overflow : (centsSum index).fails (Resolved.EvalContext.bound []) (scanOf db position table) = true)
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run (query sumCents sumCents_one) env).returnsResult property ∧
      ((db.run (query sumCents sumCents_one) env).returnsError code ↔
        code ExecutionError.integerOverflow.primaryCode) := by
  exact Run.query_overflow_calmTable (script := sumCents) rfl sumCents_one db env (sumCents_resolved db env found column) rfl
    (Database.table_of_findTable _ _ _ _ found) (sumQuery_calm position index) rfl rfl rfl
    (by rw [Resolved.Query.aggregateOf_fails, Resolved.filtered_of_filter_none _ (query := sumQuery position index) rfl]; exact overflow) rfl property code

/-- A09 for {lit}`sum`, the three claims: for every database as in {name}`sumCents_results`,

* {lit}`Fails` of {name}`sumCents` holds exactly when the sum over the scan fails: an integer sum
  leaves the 64-bit range and no REAL value follows;
* {lit}`Holds` of it holds exactly when the sum does not fail, also for a table without a row;
* {lit}`Empty` of it does not hold.

Proof sketch: {name}`sumCents_results` and {name}`sumCents_overflow` in the default environment
through {name}`Run.send_returnsResult_iff_query` and {name}`Run.send_returnsError_iff_query`; a
claim that holds excludes the others ({name}`Holds.not_fails`, {name}`Holds.not_empty`). -/
theorem sumCents_claims (db : Database) {position index : Nat} {table : CatalogTable}
    (found : db.raw.catalog.findTable (name! "ledger") = some (position, table))
    (column : columnPosition table.columns (name! "cents") = some index) :
    (Fails sumCents db ↔ (centsSum index).fails (Resolved.EvalContext.bound []) (scanOf db position table) = true) ∧
      (Holds sumCents db ↔ (centsSum index).fails (Resolved.EvalContext.bound []) (scanOf db position table) = false) ∧
      ¬ Belay.Sqlite.Empty sumCents db := by
  have result (safe : (centsSum index).fails (Resolved.EvalContext.bound []) (scanOf db position table) = false) :
      Holds sumCents db :=
    (Run.send_returnsResult_iff_query sumCents_one db _ _).mpr
      ((sumCents_results db _ found column safe _).mpr (by simp))
  have error (overflow : (centsSum index).fails (Resolved.EvalContext.bound []) (scanOf db position table) = true) :=
    sumCents_overflow db Env.default found column overflow
  cases fails : (centsSum index).fails (Resolved.EvalContext.bound []) (scanOf db position table)
  · exact ⟨⟨fun failed => absurd failed (Holds.not_fails (result fails)), nofun⟩, ⟨fun _ => rfl, fun _ => result fails⟩,
      Holds.not_empty (result fails)⟩
  · refine ⟨⟨fun _ => rfl, fun _ => (Run.send_returnsError_iff_query sumCents_one db _ _).mpr
      ((error fails (fun _ => True) _).2.mpr trivial)⟩, ⟨fun holds => ?_, nofun⟩, fun empty => ?_⟩
    · exact absurd ((Run.send_returnsResult_iff_query sumCents_one db _ _).mp holds) (error fails _ (fun _ => True)).1
    · exact absurd ((Run.send_returnsResult_iff_query sumCents_one db _ _).mp empty) (error fails _ (fun _ => True)).1

#print axioms sumCents_resolved
#print axioms sumCents_results
#print axioms sumCents_overflow
#print axioms sumCents_claims

end SelectSumCases
