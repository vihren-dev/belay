import Belay.Sqlite.Model.Programs.Claims.QueryOutputCases
import Belay.Sqlite.Model.Programs.Claims.OutputResultsLaws
import Belay.Sqlite.Model.Queries.Evaluation.PossibleResultsLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every query and statement data whose query has source rows {lit}`source`, the output of the
query is an error ({name}`Output.isError`) exactly when the run has a window mismatch, an overflow
or a failing function. Proof sketch: the three error cases are {name}`Resolved.Query.outputOn_mismatch`,
{name}`Resolved.Query.outputOn_overflow` and {name}`Resolved.Query.outputOn_function`; in the last
case the bound window gives rows, which are no error ({name}`Output.isError_ofResults`), and a missing bound window
gives {name}`Output.unmodeled`, which is no error either. -/
theorem Resolved.Query.outputOn_isError (query : Resolved.Query) (clock : Int) (counters : Counters)
    (parameters : List Value) (database : Database) (subqueries : List Resolved.Query)
    (source : Resolved.SourceRows)
    (found : query.source (Resolved.statementContext clock counters parameters database subqueries) database = some source) :
    (query.outputOn clock counters parameters database subqueries).isError = true ↔
      ((query.run (Resolved.statementContext clock counters parameters database subqueries) source.rows).mismatch = true ∨
      (query.run (Resolved.statementContext clock counters parameters database subqueries) source.rows).overflow = true ∨
      (query.run (Resolved.statementContext clock counters parameters database subqueries) source.rows).fault = .must) := by
  unfold Resolved.Query.outputOn Resolved.Query.runOn
  simp only [found]
  by_cases mismatch : (query.run (Resolved.statementContext clock counters parameters database subqueries) source.rows).mismatch = true
  · simp [mismatch, Output.isError]
  by_cases overflow : (query.run (Resolved.statementContext clock counters parameters database subqueries) source.rows).overflow = true
  · simp [mismatch, overflow, Output.isError]
  by_cases fault : (query.run (Resolved.statementContext clock counters parameters database subqueries) source.rows).fault = .must
  · simp [mismatch, overflow, fault, Output.isError]
  have mismatch' := Bool.eq_false_iff.mpr mismatch
  have overflow' := Bool.eq_false_iff.mpr overflow
  rcases query.possibleOn clock counters parameters database subqueries with _ | results
  · simp [mismatch', overflow', fault, Output.isError]
  · have noError := Output.isError_ofResults results
    simp [mismatch', overflow', fault, noError]

end Belay.Sqlite.Model
