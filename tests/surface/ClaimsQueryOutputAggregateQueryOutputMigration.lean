import Belay.Sqlite.Model.AggregateQueryOutput
import Belay.Sqlite.Model.SimpleTableRowsOutput

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite.Model

-- Original resolvedStepOutput_aggregateTable_hasRows.
example (index position : Nat) (connection : Connection)
    (parameters : List Value) (table : Table) (condition : Option Resolved.Expr) (aggregate : Resolved.Aggregate)
    (name : String) (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query
      (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) []).Calm) :
    (resolvedStepOutput none index connection parameters
      (.query (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) [])).hasRows =
        true ↔
      aggregate.fails (Resolved.EvalContext.bound parameters) ((Resolved.sourceRows table).filter fun row =>
        condition.all fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) =
        false := by
  rw [resolvedStepOutput_aggregateTable index position connection parameters table condition aggregate name present calm]
  split <;> simp_all [Output.hasRows, Resolved.Query.aggregateOf_possibleResults, Resolved.Query.aggregateOf_filtered, Output.ofResults_singleton]

-- Original resolvedStepOutput_aggregateTable_not_hasNoRows.
example (index position : Nat) (connection : Connection)
    (parameters : List Value) (table : Table) (condition : Option Resolved.Expr) (aggregate : Resolved.Aggregate)
    (name : String) (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query
      (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) []).Calm) :
    (resolvedStepOutput none index connection parameters
      (.query (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) [])).hasNoRows =
        false := by
  rw [resolvedStepOutput_aggregateTable index position connection parameters table condition aggregate name present calm]
  split <;> simp_all [Output.hasNoRows, Resolved.Query.aggregateOf_possibleResults, Resolved.Query.aggregateOf_filtered, Output.ofResults_singleton]

-- Original resolvedStepOutput_aggregateTable_isError.
example (index position : Nat) (connection : Connection)
    (parameters : List Value) (table : Table) (condition : Option Resolved.Expr) (aggregate : Resolved.Aggregate)
    (name : String) (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query
      (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) []).Calm) :
    (resolvedStepOutput none index connection parameters
      (.query (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) [])).isError =
        true ↔
      aggregate.fails (Resolved.EvalContext.bound parameters) ((Resolved.sourceRows table).filter fun row =>
        condition.all fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) =
        true := by
  rw [resolvedStepOutput_aggregateTable index position connection parameters table condition aggregate name present calm]
  split <;> simp_all [Output.isError, Resolved.Query.aggregateOf_possibleResults, Resolved.Query.aggregateOf_filtered, Output.ofResults_singleton]

end Belay.Sqlite.Model
