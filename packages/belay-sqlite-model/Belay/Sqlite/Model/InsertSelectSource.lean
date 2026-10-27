import Belay.Sqlite.Model.SourceScanOrders
import Belay.Sqlite.Model.QueryRun
import Belay.Sqlite.Model.QueryWindow
import Belay.Sqlite.Model.PossibleResults
import Belay.Sqlite.Model.QueryFunctions
import Belay.Sqlite.Model.Execution

set_option doc.verso true

/-! The rows that the query of an INSERT produces and the failure that ends them (ADR 0019, D4,
amended 2026-10-25; task {lit}`20261024-table-rebuild`). SQLite runs an independent query as a
coroutine that the INSERT pulls from, so a row is written before the next row is read. A query that
reads the written table, an INSERT trigger and {lit}`RETURNING` make SQLite collect the whole query
in a temporary table first ({lit}`useTempTable` of {lit}`sqlite3Insert`). So a source failure after
some rows either follows their writes or happens before any write.

The model describes the orders that it can state. A query with a total {lit}`ORDER BY` has one
order. A query of one table without {lit}`ORDER BY` has the orders of
{name}`Belay.Sqlite.Model.Table.accessOrders`. A query of this kind that is neither of these has an
order that SQLite chooses, and the model describes it only when it gives at most one row. -/

namespace Belay.Sqlite.Model

/-- The errors that the query of an INSERT can end its production with: a datatype mismatch, an
integer overflow, and the error of a function. None of them is a constraint error. -/
inductive SourceFailure where
  /-- A datatype mismatch of a query. -/
  | datatypeMismatch
  /-- An integer overflow of a query. -/
  | integerOverflow
  /-- The error of a function call of a query. -/
  | functionError
  deriving DecidableEq

/-- The error of the statement for a failure of its query. -/
def SourceFailure.toError : SourceFailure → ExecutionError
  | .datatypeMismatch => .datatypeMismatch
  | .integerOverflow => .integerOverflow
  | .functionError => .functionError

/-- The rows that a query produces and the failure that follows them: the rows that the INSERT
receives before the query fails, in order, and the error that ends the production, none for a query
that ends normally. For example, a query that gives two rows and then fails with an integer overflow is
{lean}`({ rows := [[.integer 1], [.integer 2]], failure := some .integerOverflow } : SourceProduction)`. -/
structure SourceProduction where
  /-- The rows before the failure, or all rows. -/
  rows : List (List Value)
  /-- The error that stops the production after {lit}`rows`, or none. -/
  failure : Option SourceFailure
  deriving DecidableEq

namespace Resolved

/-- Whether the query reads one table by a scan, row by row, without a step that holds rows back: one
table as the only source, no compound, no aggregate, no {lit}`DISTINCT`, no {lit}`ORDER BY`, and no
{lit}`OFFSET` (after the binding of a parameter of the window, {name}`Query.bindWindow`). SQLite then evaluates the {lit}`WHERE` condition and the result columns of each row
when it reads the row, so the first row that fails stops the production. -/
def Query.scansRows (query : Query) : Bool :=
  query.compound.isNone && !query.aggregate && query.groupBy.isEmpty && query.distinct.isNone &&
    query.orderBy.isEmpty && query.offset == 0 &&
    (match query.sources with
      | [join] => (match join.source with
        | .table _ => true
        | .initialTable _ | .each .. | .subquery .. | .pragma _ => false)
      | [] | _ :: _ :: _ => false)

/-- The fault of reading one source row of a query that {name}`Query.scansRows`: the fault of the
{lit}`WHERE` condition, else, for a row that it keeps, the fault of the result columns. -/
def Query.rowFault (context : EvalContext) (query : Query) (row : List Value) : Fault :=
  let columns := (query.columns.flatMap Output.scalars).foldl (fun fault term => fault.join (term.evaluate context row).2) Fault.none
  match query.filter with
  | none => columns
  | some condition =>
    let (value, fault) := condition.evaluate context row
    if fault != .none then fault else if truthy value then columns else .none

/-- Whether the query gives its rows in an order that the model describes without a choice of
SQLite: a total {lit}`ORDER BY`, where the rows of each group of equal sort keys are the same row. -/
def Query.totallyOrdered (context : EvalContext) (query : Query) (rows : List (List Value)) : Bool :=
  !query.orderBy.isEmpty && (query.tieGroupRows context rows).all fun group => group.eraseDups.length ≤ 1

/-- Whether a {lit}`WHERE` condition has an {lit}`OR`, which SQLite may answer with several indexes
one after the other. -/
def Query.hasOrCondition (query : Query) : Bool :=
  query.filter.any (·.any fun term => term matches .or ..)

/-- The production of a query over the source rows, in one order of reading them: a query that
cannot fail gives its rows ({name}`Query.run`). A failure that SQLite finds before it gives a row is
a production without rows: a window value that is no integer, the overflow of an aggregate without
{lit}`GROUP BY`, which SQLite computes after all rows, and a failing query without {lit}`FROM`. A
query that {name}`Query.scansRows` (after the binding of its window) and fails in one row gives the rows before that row when
{lit}`streaming`, else none, because SQLite then collects all rows first. A fault that the model does not describe is none,
and so is a fault of reading the source rows themselves ({name}`SourceRows.fault`). -/
def Query.productionOver (context : EvalContext) (query : Query) (source : SourceRows) (streaming : Bool) :
    Option SourceProduction :=
  let run := query.run context source.rows
  if source.fault != .none then none
  else if run.mismatch then some { rows := [], failure := some .datatypeMismatch }
  else if run.overflow then (if query.groupBy.isEmpty then some { rows := [], failure := some .integerOverflow } else none)
  else if run.fault == .must then some { rows := [], failure := some .functionError }
  else if run.fault == .none then some { rows := run.rows, failure := none }
  else if query.filter.any (·.mayFailOn context []) then none
  else match query.bindWindow context.parameters with
    | none => none
    | some bound =>
      if !bound.scansRows then none else
      let faults := source.rows.map (bound.rowFault context)
      if faults.any (· == .may) then none
      else match faults.findIdx? (· == .must) with
        | none => none
        | some failing =>
          let before := (bound.run context (source.rows.take failing)).rows
          let reached := match bound.limit with | some limit => limit ≤ before.length | none => false
          if bound.limit == some 0 || reached then some { rows := before.take (bound.limit.getD before.length), failure := none }
          else some { rows := if streaming then before else [], failure := some .functionError }

end Resolved

/-- The productions of the query of an INSERT over the database, each once, the first being the
model's own run: one for each order in which SQLite may read the rows
({name}`Table.accessOrders`), or one for a total {lit}`ORDER BY`. With {lit}`streaming` false, SQLite
collects the rows before it writes any ({name}`Resolved.Query.productionOver`). None when the model
does not describe the query: its failure, or its order when it gives more than one row. -/
def Resolved.Query.productions (context : Resolved.EvalContext) (query : Resolved.Query) (database : Database)
    (streaming : Bool) : Option (List SourceProduction) :=
  (query.source context database).bind fun source =>
    let single := fun (production : SourceProduction) => some [production]
    match query.sources, query.compound with
    | [{ source := .table position, .. }], none =>
      (database.table position).bind fun table =>
        let orders := Table.accessOrders database.catalog position table
        let ordered := query.totallyOrdered context source.rows
        let free := query.orderBy.isEmpty && query.groupBy.isEmpty && !(query.hasOrCondition && orders.length > 1)
        if !ordered && !free then (query.productionOver context source streaming).bind fun production =>
          if production.rows.length ≤ 1 then single production else none
        else
          ((if ordered then [source] else orders.map fun order => { source with rows := order.map Row.values }).mapM
            fun candidate => query.productionOver context candidate streaming).map (·.eraseDups)
    | _, _ => (query.productionOver context source streaming).bind fun production =>
      if production.rows.length ≤ 1 || query.totallyOrdered context source.rows then single production else none

end Belay.Sqlite.Model
