import Belay.Sqlite.Model.Schema.Dispatch.SelectCalmRule

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The context in which a query statement on a connection evaluates its query when it is observed with an initial
database: the clock value 0, the counters that the statement reads, the values bound to its parameters, the database
of the connection, the subqueries, and the initial database ({name}`Resolved.statementContext`). -/
abbrev Connection.queryContextFrom (connection : Connection) (parameters : List Value) (query : Resolved.Query)
    (subqueries : List Resolved.Query) (initial : Database) : Resolved.EvalContext :=
  Resolved.statementContext 0 (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
    parameters connection.state.database subqueries (some initial)

end Belay.Sqlite.Model
