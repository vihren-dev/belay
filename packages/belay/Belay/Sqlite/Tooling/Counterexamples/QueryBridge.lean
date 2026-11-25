import Belay.Sqlite.Programs.Scripts.QueryBridge

set_option doc.verso true

/-! From {lit}`Holds`, {lit}`Empty` and {lit}`Fails` to the model's query (ADR 0017, S4): the
output of a script that starts with a statement is the output of the step of that statement
({name}`Belay.Sqlite.Model.runScriptStep_output`), and when resolution turns the statement into a
query, the claims are statements about the source rows of that query, its run and its one result.
The query forms in the modules after this one give the resolved query and these three facts. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every query script whose observed output equals the output of the query
{lit}`query` (without a clock read and without a counter read that is unknown), whose source rows
{lit}`source` and bound window {lit}`bound` exist: {lit}`Holds` of the script on the database means
that the model describes the query (its subqueries are plain and the source rows have no fault
{lit}`may`), the run of the query has no window mismatch, no overflow and no fault, and the one
result of the bound query has a row. Proof sketch: the observed output equation and
{name}`resolvedStepOutput_query_hasRows`. -/
theorem Holds.iff_query {script : Script} {db : Database} {isQuery : script.isQuery = true}
    {parameters : List Value}
    {query bound : Resolved.Query} {subqueries : List Resolved.Query}
    {source : Resolved.SourceRows}
    (observed : script.outputOn db = some (resolvedStepOutput none 0 db.raw.connection parameters
      (.query query subqueries)))
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : db.raw.connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (db.raw.connection.queryContext parameters query subqueries) db.raw = some source)
    (window : query.bindWindow parameters = some bound) :
    Holds script db isQuery ↔
      Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true ∧ source.fault ≠ .may ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).mismatch = false ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).overflow = false ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).fault = .none ∧
        bound.results (db.raw.connection.queryContext parameters query subqueries) source.rows ≠ [] := by
  rw [Holds.iff_of_outputOn
    observed isQuery]
  exact resolvedStepOutput_query_hasRows 0 db.raw.connection parameters query bound subqueries source noClock known found window

/-- For every query script whose observed output equals the output of the query
{lit}`query` (as for {name}`Holds.iff_query`): {lit}`Empty` of the script on the database means that
the model describes the query, the run has no window mismatch, no overflow and no fault, and the
one result of the bound query has no row. Proof sketch: the observed output equation and
{name}`resolvedStepOutput_query_hasNoRows`. -/
theorem Empty.iff_query {script : Script} {db : Database} {isQuery : script.isQuery = true}
    {parameters : List Value}
    {query bound : Resolved.Query} {subqueries : List Resolved.Query}
    {source : Resolved.SourceRows}
    (observed : script.outputOn db = some (resolvedStepOutput none 0 db.raw.connection parameters
      (.query query subqueries)))
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : db.raw.connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (db.raw.connection.queryContext parameters query subqueries) db.raw = some source)
    (window : query.bindWindow parameters = some bound) :
    Empty script db isQuery ↔
      Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true ∧ source.fault ≠ .may ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).mismatch = false ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).overflow = false ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).fault = .none ∧
        bound.results (db.raw.connection.queryContext parameters query subqueries) source.rows = [] := by
  rw [Empty.iff_of_outputOn
    observed isQuery]
  exact resolvedStepOutput_query_hasNoRows 0 db.raw.connection parameters query bound subqueries source noClock known found window

/-- For every query script whose observed output equals the output of the query
{lit}`query` (as for {name}`Holds.iff_query`, without a bound window): {lit}`Fails` of the script on
the database means that the model describes the query and the run has a window mismatch, an
overflow or a failing function. Proof sketch: the observed output equation and
{name}`resolvedStepOutput_query_isError`. -/
theorem Fails.iff_query {script : Script} {db : Database} {isQuery : script.isQuery = true}
    {parameters : List Value}
    {query : Resolved.Query} {subqueries : List Resolved.Query}
    {source : Resolved.SourceRows}
    (observed : script.outputOn db = some (resolvedStepOutput none 0 db.raw.connection parameters
      (.query query subqueries)))
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : db.raw.connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (db.raw.connection.queryContext parameters query subqueries) db.raw = some source) :
    Fails script db isQuery ↔
      Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true ∧ source.fault ≠ .may ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).fault ≠ .may ∧
        ((query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).mismatch = true ∨
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).overflow = true ∨
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).fault = .must) := by
  rw [Fails.iff_of_outputOn
    observed isQuery]
  exact resolvedStepOutput_query_isError 0 db.raw.connection parameters query subqueries source noClock known found

end Belay.Sqlite
