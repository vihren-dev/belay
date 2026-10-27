import Belay.Sqlite.Model.InsertSelectSource
import Belay.Sqlite.Model.SimpleQueryLaws
import Belay.Sqlite.Model.TableSourceLaws

set_option doc.verso true

/-! The productions of a plain scan (ADR 0017, S6; task {lit}`20261027-schema-script-laws`). The query
of an INSERT that only selects columns of one table, with an optional {lit}`WHERE` condition, no fallible
call and no subquery fault, cannot fail. Each order in which SQLite may read the table
({lit}`Table.accessOrders`) gives the rows that the query selects from that order, and no failure. When the
orders give equal rows, the production is certain: one production, with no failure. -/

namespace Belay.Sqlite.Model

/-- For every quiet context, simple query of the first source of a table without a fallible call, database
that has the table at that position, and choice of streaming: if the condition does not have an
{lit}`OR` while the table has several access orders (a condition that SQLite may answer with several
indexes), the productions of the query ({name}`Resolved.Query.productions`) are the rows that the query
selects from each access order of the table ({name}`Table.accessOrders`), each once, with no failure.
Proof sketch: the source rows of the query are the rows of the table in scan order
({name}`Resolved.Query.source_first`); the run over the rows of each order has no fault, mismatch or overflow
({name}`Resolved.Query.Simple.run_plain`), so each order gives its results without a failure. -/
theorem Resolved.Query.productions_scan (context : Resolved.EvalContext) (query : Resolved.Query) (database : Database)
    (position : Nat) (table : Table) (streaming : Bool) (sources : query.sources = [Resolved.QuerySource.first position])
    (simple : query.Simple) (plain : query.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true)
    (quiet : context.Quiet) (present : database.table position = some table)
    (noChoice : (query.hasOrCondition && decide ((Table.accessOrders database.catalog position table).length > 1)) = false) :
    query.productions context database streaming =
      some (((Table.accessOrders database.catalog position table).map fun order =>
        ({ rows := query.results context (order.map Row.values), failure := none } : SourceProduction)).eraseDups) := by
  have source := Resolved.Query.source_first context query database position table sources present
  unfold Resolved.Query.productions
  rw [source]
  simp only [Option.bind_some, sources, Resolved.QuerySource.first]
  have ordered : query.totallyOrdered context (sourceRows table) = false := by
    simp [Resolved.Query.totallyOrdered, simple.orderBy]
  have each : ∀ order : List Row, query.productionOver context
      { rows := order.map Row.values, width := table.shape.columns.length, fault := Fault.none } streaming =
      some { rows := query.results context (order.map Row.values), failure := none } := by
    intro order
    simp [Resolved.Query.productionOver, simple.run_plain context quiet plain]
  rw [ordered]
  simp only [simple.compound, present, Option.bind_some, simple.orderBy, simple.groupBy, List.isEmpty_nil,
    Bool.not_false, Bool.true_and, Bool.not_true, noChoice, Bool.false_eq_true, ite_false]
  rw [List.mapM_map]
  simp only [Function.comp_def, each]
  have mapped : ∀ orders : List (List Row), orders.mapM
      (fun order => some ({ rows := query.results context (order.map Row.values), failure := none } : SourceProduction)) =
      some (orders.map fun order => { rows := query.results context (order.map Row.values), failure := none }) := by
    intro orders
    induction orders with
    | nil => rfl
    | cons order rest ih => simp [List.mapM_cons, ih]
  rw [mapped]
  rfl

/-- For every table and catalog whose access keys all give the rows of the table in the order of its scan
(comparing the rowids), the table has one access order, the scan ({name}`Table.accessOrders`). For example, a
table with no index and no key besides its scan has the one order. Proof sketch: the fold of
{name}`Table.accessOrders` keeps the list with the scan alone whenever the next order has the rowids of the
scan. -/
theorem Table.accessOrders_single (catalog : Catalog) (position : Nat) (table : Table)
    (same : ∀ access ∈ catalog.accessKeys position table.shape,
      (Table.indexOrder table.scanRows access.1 access.2).map Row.rowid = table.scanRows.map Row.rowid) :
    Table.accessOrders catalog position table = [table.scanRows] := by
  unfold Table.accessOrders
  simp only [List.foldl_cons]
  have step : ∀ (orders : List (List Row)), (∀ order ∈ orders, order.map Row.rowid = table.scanRows.map Row.rowid) →
      orders.foldl (fun found order => if found.any (fun other => other.map (·.rowid) == order.map (·.rowid)) then found
        else found ++ [order]) [table.scanRows] = [table.scanRows] := by
    intro orders
    induction orders with
    | nil => intro _; rfl
    | cons order rest ih =>
      intro every
      simp only [List.foldl_cons, List.any_cons, List.any_nil, Bool.or_false]
      rw [every order (List.mem_cons_self ..)]
      simp only [beq_self_eq_true, ite_true]
      exact ih fun other member => every other (List.mem_cons_of_mem _ member)
  have rowids : ∀ order ∈ (catalog.accessKeys position table.shape).map
      fun (keys, filter) => Table.indexOrder table.scanRows keys filter, order.map Row.rowid = table.scanRows.map Row.rowid := by
    intro order member
    obtain ⟨access, accessMember, rfl⟩ := List.mem_map.mp member
    exact same access accessMember
  simp only [List.any_nil, Bool.false_eq_true, ite_false, List.nil_append]
  exact step _ rowids

/-- For every quiet context, simple query of the first source of a table without a fallible call, and database
whose table at that position has one access order, the scan ({name}`Table.accessOrders`), the productions of
the query ({name}`Resolved.Query.productions`) are exactly one: the rows that the query selects from the table in scan
order, with no failure. The production is certain. Proof sketch: {name}`Resolved.Query.productions_scan` with
one order, which has no choice for a condition with {lit}`OR`. -/
theorem Resolved.Query.productions_scan_single (context : Resolved.EvalContext) (query : Resolved.Query)
    (database : Database) (position : Nat) (table : Table) (streaming : Bool)
    (sources : query.sources = [Resolved.QuerySource.first position]) (simple : query.Simple)
    (plain : query.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true) (quiet : context.Quiet)
    (present : database.table position = some table)
    (single : Table.accessOrders database.catalog position table = [table.scanRows]) :
    query.productions context database streaming =
      some [{ rows := query.results context (sourceRows table), failure := none }] := by
  rw [query.productions_scan context database position table streaming sources simple plain quiet present
    (by rw [single]; simp), single]
  rfl

end Belay.Sqlite.Model
