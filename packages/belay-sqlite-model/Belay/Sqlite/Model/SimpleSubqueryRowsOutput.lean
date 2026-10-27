import Belay.Sqlite.Model.SimpleTableRowsOutput
import Belay.Sqlite.Model.SimpleQuerySteps

set_option doc.verso true

/-! The exact output of a calm simple query statement with subqueries (task 20261027): its step gives the rows of the
one result of the query in normal form, in the context of the statement, when no expression of the query has a fault.
{name}`Belay.Sqlite.Model.resolvedStepOutput_simple_rows` is the same law for a statement without subqueries. -/

namespace Belay.Sqlite.Model

/-- For every connection, values and calm statement of a simple query with subqueries, over source rows of the query
that have no fault, when no expression of the query has a fault over the empty row and over each source row in the
context of the statement, the output of its step with any clock and index is the rows of the one result of the query
over those rows, in normal form, in the context of the statement. Proof sketch: as for
{name}`resolvedStepOutput_simple_rows`: the run has no fault ({name}`Resolved.Query.Simple.run_of_faultless`), so the
model describes the statement and {name}`Resolved.Query.outputOn_clean` gives the possible results of
{name}`Resolved.Query.Simple.possibleResults_eq`. -/
theorem resolvedStepOutput_simple_rows_of_faultless (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) (query : Resolved.Query) (subqueries : List Resolved.Query) (simple : query.Simple)
    (source : Resolved.SourceRows) (calm : (Resolved.Statement.query query subqueries).Calm)
    (found : query.source (connection.queryContext parameters query subqueries) connection.state.database = some source)
    (clean : source.fault = .none)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate (connection.queryContext parameters query subqueries) row).2 = .none) :
    resolvedStepOutput clock index connection parameters (.query query subqueries) =
      .rows (Resolved.normalForm (query.results (connection.queryContext parameters query subqueries) source.rows)) := by
  have run := simple.run_of_faultless (connection.queryContext parameters query subqueries) calm.query_plain
    source.rows faultless
  rw [resolvedStepOutput_clock_free clock index _ _ _ calm.readsClock,
    resolvedStepOutput_query index connection parameters query subqueries calm.readsClock (calm.firstUnknown _)]
  have hrun := connection.runOn_of_found parameters query subqueries source found
  have described : query.described 0
      (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads) parameters
      connection.state.database subqueries = true := by
    unfold Resolved.Query.described
    rw [hrun, run]
    simp [calm.subqueries_plain, clean]
  split
  · rw [Resolved.Query.outputOn_clean query 0 _ parameters connection.state.database subqueries source query found
        (simple.bindWindow parameters) (by rw [run]) (by rw [run]) (by rw [run]; simp),
      simple.possibleResults_eq, Output.ofResults_singleton]
  · rename_i notDescribed
    exact absurd described notDescribed

end Belay.Sqlite.Model
