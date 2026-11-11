import Belay.Sqlite.Model.Schema.Rows.InsertSelectSource
import Belay.Sqlite.Model.Queries.Evaluation.PlainQueryRules
import Belay.Sqlite.Model.Schema.Dispatch.PlainQueryRules
import Belay.Sqlite.Model.Schema.Dispatch.TableSourceLaws

set_option doc.verso true

/-! The productions of a plain scan (ADR 0017, S6; task {lit}`20261027-schema-script-laws`). The query
of an INSERT that only selects columns of one table, with an optional {lit}`WHERE` condition, no fallible
call and no subquery fault, cannot fail. Each order in which SQLite may read the table
({lit}`Table.accessOrders`) gives the rows that the query selects from that order, and no failure. When the
orders give equal rows, the production is certain: one production, with no failure. -/

namespace Belay.Sqlite.Model

/-- For every quiet context, query of the first source of a table that is no compound and has no ordering,
grouping, aggregation, {lit}`DISTINCT` or window parameter, and no fallible call, database
that has the table at that position, and choice of streaming: if the condition does not have an
{lit}`OR` while the table has several access orders (a condition that SQLite may answer with several
indexes), the productions of the query ({name}`Resolved.Query.productions`) are the rows that the query
selects from each access order of the table ({name}`Table.accessOrders`), each once, with no failure.
Proof sketch: the source rows of the query are the rows of the table in scan order
({name}`Resolved.Query.source_first`); the run over the rows of each order has no fault, mismatch or overflow
({name}`Resolved.Query.run_quiet`), so each order gives its results without a failure. -/
theorem Resolved.Query.productions_scan (context : Resolved.EvalContext) (query : Resolved.Query) (database : Database)
    (position : Nat) (table : Table) (streaming : Bool) (sources : query.sources = [Resolved.QuerySource.first position])
    (single : query.compound = none) (unordered : query.orderBy = [])
    (ungrouped : query.groupBy = []) (noAggregate : query.aggregate = false) (noDistinct : query.distinct = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (plain : query.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true)
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
    simp [Resolved.Query.totallyOrdered, unordered]
  have each : ∀ order : List Row, query.productionOver context
      { rows := order.map Row.values, width := table.shape.columns.length, fault := Fault.none } streaming =
      some { rows := query.results context (order.map Row.values), failure := none } := by
    intro order
    simp [Resolved.Query.productionOver, Resolved.Query.run_quiet context quiet single limitParameter offsetParameter plain
      (by simp [Resolved.Query.fails, noAggregate]) (by simp [Resolved.Query.distinctCertain, noDistinct])]
  rw [ordered]
  simp only [single, present, Option.bind_some, unordered, ungrouped, List.isEmpty_nil,
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

/-- For every quiet context, query as in {name}`Resolved.Query.productions_scan`, and database
whose table at that position has one access order, the scan ({name}`Table.accessOrders`), the productions of
the query ({name}`Resolved.Query.productions`) are exactly one: the rows that the query selects from the table in scan
order, with no failure. The production is certain. Proof sketch: {name}`Resolved.Query.productions_scan` with
one order, which has no choice for a condition with {lit}`OR`. -/
theorem Resolved.Query.productions_scan_single (context : Resolved.EvalContext) (query : Resolved.Query)
    (database : Database) (position : Nat) (table : Table) (streaming : Bool)
    (sources : query.sources = [Resolved.QuerySource.first position]) (single : query.compound = none) (unordered : query.orderBy = [])
    (ungrouped : query.groupBy = []) (noAggregate : query.aggregate = false) (noDistinct : query.distinct = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (plain : query.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true) (quiet : context.Quiet)
    (present : database.table position = some table)
    (oneOrder : Table.accessOrders database.catalog position table = [table.scanRows]) :
    query.productions context database streaming =
      some [{ rows := query.results context (sourceRows table), failure := none }] := by
  rw [query.productions_scan context database position table streaming sources single unordered ungrouped
    noAggregate noDistinct limitParameter offsetParameter plain quiet present
    (by rw [oneOrder]; simp), oneOrder]
  rfl

end Belay.Sqlite.Model
