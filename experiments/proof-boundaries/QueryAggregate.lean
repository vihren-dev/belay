import QuerySemantic
import Belay.Sqlite.Model.AggregateQueryLaws
import Belay.Sqlite.Model.SimpleQuerySteps
import Belay.Sqlite.Model.TableSourceLaws

set_option doc.verso true

namespace ProofBoundaries
open Belay.Sqlite Belay.Sqlite.Model

section
variable (index position : Nat) (connection : Connection) (parameters : List Value)
  (table : Table) (condition : Option Resolved.Expr) (aggregate : Resolved.Aggregate) (name : String)
  (present : connection.state.database.table position = some table)
  (calm : (Resolved.Statement.query
    (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) []).Calm)
include present calm

/-- Under the original aggregate-table premises, the exact output is integer overflow
when the aggregate fails; otherwise it contains every possible result of the aggregate.
Proof sketch: characterize the aggregate run once and use the common source-output law. -/
theorem aggregate_output :
    let query := Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name
    let context := Resolved.EvalContext.bound parameters
    resolvedStepOutput none index connection parameters (.query query []) =
      if aggregate.fails context ((Resolved.sourceRows table).filter fun row =>
          condition.all fun expression => Resolved.truthy (expression.eval context row)) then
        .error ExecutionError.integerOverflow.primaryCode
      else Output.ofResults (query.possibleResults context (Resolved.sourceRows table)) := by
  dsimp only
  have found := Resolved.Query.source_first (connection.queryContext parameters
    (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) [])
    (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name)
    connection.state.database position table rfl present
  rw [query_source_output index connection parameters _ [] _ calm.readsClock (calm.firstUnknown _) found,
    Resolved.Query.aggregateOf_run_of_faultless _ _ _ _ _ calm.query_plain _ (calm.faultless_nil connection parameters)]
  simp only [calm.subqueries_plain, Bool.true_and, Resolved.Query.aggregateOf_bindWindow,
    Connection.queryContext_of_calm connection parameters _ calm, Resolved.Query.aggregateOf_filtered]
  simp

/-- Under the original aggregate-table premises, rows exist exactly when the aggregate
does not fail. Proof sketch: the output certificate gives either an error or a one-row result. -/
theorem aggregate_hasRows :
    (resolvedStepOutput none index connection parameters
      (.query (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) [])).hasRows = true ↔
      aggregate.fails (Resolved.EvalContext.bound parameters) ((Resolved.sourceRows table).filter fun row =>
        condition.all fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) = false := by
  rw [aggregate_output index position connection parameters table condition aggregate name present calm]
  split
  · simp_all [Output.hasRows]
  · rw [Output.hasRows_possibleResults, Resolved.Query.aggregateOf_results]
    simp_all

/-- Under the original aggregate-table premises, the output never reports no rows.
Proof sketch: neither the overflow error nor a result with one row is an empty result. -/
theorem aggregate_not_empty :
    (resolvedStepOutput none index connection parameters
      (.query (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) [])).hasNoRows = false := by
  rw [aggregate_output index position connection parameters table condition aggregate name present calm]
  split
  · rfl
  · apply Bool.eq_false_iff.mpr
    intro empty
    rw [Output.hasNoRows_possibleResults, Resolved.Query.aggregateOf_results] at empty
    cases empty

/-- Under the original aggregate-table premises, the output is an error exactly when
the aggregate fails. Proof sketch: inspect the exact output certificate's two cases. -/
theorem aggregate_is_error :
    (resolvedStepOutput none index connection parameters
      (.query (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) [])).isError = true ↔
      aggregate.fails (Resolved.EvalContext.bound parameters) ((Resolved.sourceRows table).filter fun row =>
        condition.all fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) = true := by
  rw [aggregate_output index position connection parameters table condition aggregate name present calm]
  split
  · simp_all [Output.isError]
  · rw [Output.isError_ofResults]
    simp_all

end
#print axioms aggregate_output
#print axioms aggregate_hasRows
#print axioms aggregate_not_empty
#print axioms aggregate_is_error
end ProofBoundaries
