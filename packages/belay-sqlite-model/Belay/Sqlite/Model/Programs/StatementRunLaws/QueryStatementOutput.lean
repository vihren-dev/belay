import Belay.Sqlite.Model.Programs.Scripts.QueryOutputFacts
import Belay.Sqlite.Model.Queries.Evaluation.QueryOutputFacts

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every query statement that reads no clock and no unknown counter, whose source rows
{lit}`source` exist, the output of its step is an error exactly when the model describes the statement
and the run has a window mismatch, an overflow or a failing function. Proof sketch:
{name}`resolvedStepOutput_query` and {name}`Resolved.Query.outputOn_isError`; an output that is
{name}`Output.unmodeled` is no error. -/
theorem resolvedStepOutput_query_isError (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (subqueries : List Resolved.Query) (source : Resolved.SourceRows)
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (connection.queryContext parameters query subqueries) connection.state.database = some source) :
    (resolvedStepOutput none index connection parameters (.query query subqueries)).isError = true ↔
      Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true ∧ source.fault ≠ .may ∧
        (query.run (connection.queryContext parameters query subqueries) source.rows).fault ≠ .may ∧
        ((query.run (connection.queryContext parameters query subqueries) source.rows).mismatch = true ∨
        (query.run (connection.queryContext parameters query subqueries) source.rows).overflow = true ∨
        (query.run (connection.queryContext parameters query subqueries) source.rows).fault = .must) := by
  rw [resolvedStepOutput_query index connection parameters query subqueries noClock known]
  have hrun := connection.runOn_of_found parameters query subqueries source found
  unfold Resolved.Query.described
  rw [hrun]
  by_cases plain : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true
  · by_cases srcFault : source.fault = .may
    · simp [plain, srcFault, Output.isError]
    · by_cases runFault : (query.run (connection.queryContext parameters query subqueries) source.rows).fault = .may
      · simp [plain, runFault, Output.isError]
      · simp [plain, srcFault, runFault, Resolved.Query.outputOn_isError _ _ _ _ _ _ _ found]
  · simp [plain, Output.isError]

end Belay.Sqlite.Model
