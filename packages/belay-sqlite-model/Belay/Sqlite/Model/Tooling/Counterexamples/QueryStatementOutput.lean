import Belay.Sqlite.Model.Programs.Scripts.QueryOutputFacts
import Belay.Sqlite.Model.Queries.Evaluation.QueryStatementOutput
import Belay.Sqlite.Model.Tooling.Counterexamples.QueryOutputRows

set_option doc.verso true

/-! Row and error projections of query statement outputs. -/

namespace Belay.Sqlite.Model

/-- For every query statement that reads no clock and no unknown counter, whose source rows
{lit}`source` and bound window {lit}`bound` exist, the output of its step has rows exactly when
all of these hold: the subqueries of the query are plain, the source rows have no fault
{lit}`may`, the run of the query has no window mismatch, no overflow and no fault, and the one
result of the bound query has a row. Proof sketch: {name}`resolvedStepOutput_query` and
{name}`Resolved.Query.outputOn_hasRows`; the model describes a run only when its fault is not
{lit}`may`, and a fault that is neither {lit}`may` nor {lit}`must` is none
({name}`Resolved.Fault.ne_must_iff_none`). -/
theorem resolvedStepOutput_query_hasRows (index : Nat) (connection : Connection) (parameters : List Value)
    (query bound : Resolved.Query) (subqueries : List Resolved.Query) (source : Resolved.SourceRows)
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (connection.queryContext parameters query subqueries) connection.state.database = some source)
    (window : query.bindWindow parameters = some bound) :
    (resolvedStepOutput none index connection parameters (.query query subqueries)).hasRows = true ↔
      Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true ∧ source.fault ≠ .may ∧
        (query.run (connection.queryContext parameters query subqueries) source.rows).mismatch = false ∧
        (query.run (connection.queryContext parameters query subqueries) source.rows).overflow = false ∧
        (query.run (connection.queryContext parameters query subqueries) source.rows).fault = .none ∧
        bound.results (connection.queryContext parameters query subqueries) source.rows ≠ [] := by
  rw [resolvedStepOutput_query index connection parameters query subqueries noClock known]
  have hrun := connection.runOn_of_found parameters query subqueries source found
  unfold Resolved.Query.described
  rw [hrun]
  by_cases plain : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true
  · by_cases srcFault : source.fault = .may
    · simp [plain, srcFault, Output.hasRows]
    · by_cases runFault : (query.run (connection.queryContext parameters query subqueries) source.rows).fault = .may
      · simp [plain, runFault, Output.hasRows]
      · simp [plain, srcFault, runFault, Resolved.Fault.ne_must_iff_none _ runFault, Resolved.Query.outputOn_hasRows _ _ _ _ _ _ _ _ found window]
  · simp [plain, Output.hasRows]

/-- For every query statement that reads no clock and no unknown counter, whose source rows
{lit}`source` and bound window {lit}`bound` exist, the output of its step has no rows exactly when
all of these hold: the subqueries of the query are plain, the source rows have no fault
{lit}`may`, the run of the query has no window mismatch, no overflow and no fault, and the one
result of the bound query has no row. Proof sketch: {name}`resolvedStepOutput_query` and
{name}`Resolved.Query.outputOn_hasNoRows`; the model describes a run only when its fault is not
{lit}`may`, and a fault that is neither {lit}`may` nor {lit}`must` is none
({name}`Resolved.Fault.ne_must_iff_none`). -/
theorem resolvedStepOutput_query_hasNoRows (index : Nat) (connection : Connection) (parameters : List Value)
    (query bound : Resolved.Query) (subqueries : List Resolved.Query) (source : Resolved.SourceRows)
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (connection.queryContext parameters query subqueries) connection.state.database = some source)
    (window : query.bindWindow parameters = some bound) :
    (resolvedStepOutput none index connection parameters (.query query subqueries)).hasNoRows = true ↔
      Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true ∧ source.fault ≠ .may ∧
        (query.run (connection.queryContext parameters query subqueries) source.rows).mismatch = false ∧
        (query.run (connection.queryContext parameters query subqueries) source.rows).overflow = false ∧
        (query.run (connection.queryContext parameters query subqueries) source.rows).fault = .none ∧
        bound.results (connection.queryContext parameters query subqueries) source.rows = [] := by
  rw [resolvedStepOutput_query index connection parameters query subqueries noClock known]
  have hrun := connection.runOn_of_found parameters query subqueries source found
  unfold Resolved.Query.described
  rw [hrun]
  by_cases plain : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true
  · by_cases srcFault : source.fault = .may
    · simp [plain, srcFault, Output.hasNoRows]
    · by_cases runFault : (query.run (connection.queryContext parameters query subqueries) source.rows).fault = .may
      · simp [plain, runFault, Output.hasNoRows]
      · simp [plain, srcFault, runFault, Resolved.Fault.ne_must_iff_none _ runFault, Resolved.Query.outputOn_hasNoRows _ _ _ _ _ _ _ _ found window]
  · simp [plain, Output.hasNoRows]

end Belay.Sqlite.Model
