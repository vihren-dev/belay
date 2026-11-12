import Belay.Sqlite.Model.Queries.Evaluation.QueryOutputFacts
import Belay.Sqlite.Model.Schema.Dispatch.QueryOutputFacts
import Belay.Sqlite.Model.Queries.Evaluation.PlainQueryRules
import Belay.Sqlite.Model.Schema.Dispatch.PlainQueryRules

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The readiness of a query statement on a connection at a clock value with the values bound to
its parameters ({name}`Connection.queryContextAt`), with its source rows {lit}`source` and its
bound query {lit}`bound`: each field is one condition under which the step outputs every result
that the model permits. -/
structure Connection.SelectReady (connection : Connection) (value : Int) (parameters : List Value)
    (query : Resolved.Query) (subqueries : List Resolved.Query) (source : Resolved.SourceRows)
    (bound : Resolved.Query) : Prop where
  /-- Each counter that the statement reads has a known value. -/
  known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none
  /-- The query has the source rows {lit}`source` in the context of the statement. -/
  found : query.source (connection.queryContextAt value parameters query subqueries) connection.state.database =
    some source
  /-- No nested subquery has a fallible call ({name}`Resolved.subqueriesPlain`). -/
  plain : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true
  /-- The source rows do not possibly fail. -/
  sourceCertain : source.fault ≠ .may
  /-- The window binds to the query {lit}`bound` with the values ({name}`Resolved.Query.bindWindow`). -/
  window : query.bindWindow parameters = some bound
  /-- The run has no window mismatch. -/
  mismatch : (query.run (connection.queryContextAt value parameters query subqueries) source.rows).mismatch = false
  /-- The run has no overflow. -/
  overflow : (query.run (connection.queryContextAt value parameters query subqueries) source.rows).overflow = false
  /-- The run has no fault, neither certain nor possible. -/
  fault : (query.run (connection.queryContextAt value parameters query subqueries) source.rows).fault = .none

end Belay.Sqlite.Model
