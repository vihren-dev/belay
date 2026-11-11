import Belay.Sqlite.Model.Schema.Dispatch.Connection

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whether the model describes a query statement on a database, with the counters that it reads: its
subqueries (those that are no term of a compound) have no fallible call, and neither the source
rows nor the run of the query have the fault {name}`Resolved.Fault.may`. It is the support check of
{name}`runStatement` for a query. -/
def Resolved.Query.described (query : Resolved.Query) (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Database) (subqueries : List Resolved.Query) : Bool :=
  Resolved.subqueriesPlain (query.nestedSubqueries subqueries) &&
    (query.runOn clock counters parameters database subqueries).all fun (source, run) =>
      source.fault != .may && run.fault != .may

/-- The context in which a query statement evaluates its query on the connection at a clock value:
the counters that the statement reads, the values bound to its parameters, the database of the
connection and the subqueries ({name}`Resolved.statementContext`). -/
abbrev Connection.queryContextAt (connection : Connection) (value : Int) (parameters : List Value)
    (query : Resolved.Query) (subqueries : List Resolved.Query) : Resolved.EvalContext :=
  Resolved.statementContext value
    (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
    parameters connection.state.database subqueries

/-- The context in which a query statement evaluates its query on the connection, without a clock:
{name}`Connection.queryContextAt` at the clock value 0. -/
abbrev Connection.queryContext (connection : Connection) (parameters : List Value) (query : Resolved.Query)
    (subqueries : List Resolved.Query) : Resolved.EvalContext :=
  connection.queryContextAt 0 parameters query subqueries

/-- For every query statement whose query has source rows {lit}`source`, the run of the query on the
connection is the run over these rows. Proof sketch: unfold {name}`Resolved.Query.runOn` and rewrite
with the hypothesis {lit}`found`. -/
theorem Connection.runOn_of_found (connection : Connection) (parameters : List Value) (query : Resolved.Query)
    (subqueries : List Resolved.Query) (source : Resolved.SourceRows)
    (found : query.source (connection.queryContext parameters query subqueries) connection.state.database = some source) :
    query.runOn 0 (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
      parameters connection.state.database subqueries =
      some (source, query.run (connection.queryContext parameters query subqueries) source.rows) := by
  simp [Resolved.Query.runOn, found]

end Belay.Sqlite.Model
