import Belay.Sqlite.Model.SimpleQueryLaws
import Belay.Sqlite.Model.QueryStatementOutput
import Belay.Sqlite.Model.StatementCalm

set_option doc.verso true

namespace ProofBoundaries
open Belay.Sqlite Belay.Sqlite.Model

/-- For every optional output equal to a known output, any property of the observed output
is equivalent to that property of the known output. Proof sketch: substitute the equality. -/
theorem observe_eq {observed : Option Output} {output : Output}
    (same : observed = some output) (property : Output → Prop) :
    (∃ value, observed = some value ∧ property value) ↔ property output := by
  simp [same]

/-- For every optional output equal to a known output, any Boolean observer gives the same
answer on the known output. Proof sketch: substitute the equality and evaluate the option. -/
theorem observe_test_eq {observed : Option Output} {output : Output}
    (same : observed = some output) (test : Output → Bool) :
    observed.any test = true ↔ test output = true := by
  simp [same]

/-- For a clock-independent query with known counters and a source, its exact output
first checks support, then mismatch, overflow and certain function failure, then the
optional window and all possible results. The window need not bind. Proof sketch: unfold
the existing query-output equation once using the supplied source. -/
theorem query_source_output (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (subqueries : List Resolved.Query) (source : Resolved.SourceRows)
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (connection.queryContext parameters query subqueries)
      connection.state.database = some source) :
    let context := connection.queryContext parameters query subqueries
    let run := query.run context source.rows
    resolvedStepOutput none index connection parameters (.query query subqueries) =
      if Resolved.subqueriesPlain (query.nestedSubqueries subqueries) &&
          (source.fault != .may && run.fault != .may) then
        if run.mismatch then .error ExecutionError.datatypeMismatch.primaryCode
        else if run.overflow then .error ExecutionError.integerOverflow.primaryCode
        else if run.fault == .must then .error ExecutionError.functionError.primaryCode
        else match query.bindWindow parameters with
          | none => .unmodeled "the model gives no result for this query"
          | some bound => Output.ofResults (bound.possibleResults context source.rows)
      else .unmodeled unmodeledHere := by
  rw [resolvedStepOutput_query index connection parameters query subqueries noClock known]
  simp only [Resolved.Query.described, Resolved.Query.outputOn, Resolved.Query.runOn,
    Resolved.Query.possibleOn, found, Option.bind_some]
  cases query.bindWindow parameters <;> rfl

/-- For every simple calm query with source rows and faultless expressions, the complete
output is unmodeled when the source may fail; otherwise it contains every possible result.
No clean-source assumption is needed. Proof sketch: characterize the query run once, then
use its exact output; this preserves result choices instead of selecting one result. -/
theorem simple_output (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (subqueries : List Resolved.Query) (simple : query.Simple)
    (source : Resolved.SourceRows) (calm : (Resolved.Statement.query query subqueries).Calm)
    (found : query.source (connection.queryContext parameters query subqueries)
      connection.state.database = some source)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate (connection.queryContext parameters query subqueries) row).2 = .none) :
    resolvedStepOutput none index connection parameters (.query query subqueries) =
      if source.fault = .may then .unmodeled unmodeledHere else
        Output.ofResults (query.possibleResults
          (connection.queryContext parameters query subqueries) source.rows) := by
  have run := simple.run_of_faultless _ calm.query_plain source.rows faultless
  rw [query_source_output index connection parameters query subqueries source calm.readsClock
    (calm.firstUnknown _) found]
  simp only [run, simple.bindWindow, calm.subqueries_plain, Bool.true_and]
  by_cases sourceMay : source.fault = .may
  · simp [sourceMay]
  · simp [sourceMay]

/-- Under the simple-output hypotheses, source faults do not turn the output into an error.
The may-fault case remains unmodeled. Proof sketch: split the exact output characterization. -/
theorem simple_no_error (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (subqueries : List Resolved.Query) (simple : query.Simple)
    (source : Resolved.SourceRows) (calm : (Resolved.Statement.query query subqueries).Calm)
    (found : query.source (connection.queryContext parameters query subqueries)
      connection.state.database = some source)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate (connection.queryContext parameters query subqueries) row).2 = .none) :
    (resolvedStepOutput none index connection parameters (.query query subqueries)).isError = false := by
  rw [simple_output index connection parameters query subqueries simple source calm found faultless]
  split
  · rfl
  · exact Output.isError_ofResults _

#print axioms observe_eq
#print axioms observe_test_eq
#print axioms query_source_output
#print axioms simple_output
#print axioms simple_no_error
end ProofBoundaries
