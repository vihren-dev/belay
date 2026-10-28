import Belay.Sqlite.Model.AggregateQueryLaws
import Belay.Sqlite.Model.SimpleQuerySteps
import Belay.Sqlite.Model.TableSourceLaws

set_option doc.verso true

/-! The output of a whole-table aggregate query statement over a table (ADR 0017, S4): a calm statement
{lit}`SELECT agg(x) FROM t WHERE p` has one row exactly when the aggregate does not fail over the rows that
{lit}`WHERE` keeps, is an error exactly when it fails, and never has no row. -/

namespace Belay.Sqlite.Model

/-- For every calm whole-table aggregate statement over an existing table, the complete
output is the integer-overflow error when the aggregate fails on the kept rows; otherwise it
gives every possible result of that aggregate query. The source filter runs before aggregation,
including on empty input. Proof sketch: substitute the table source and fault-free aggregate run
in the complete source-output equation. -/
theorem resolvedStepOutput_aggregateTable (index position : Nat) (connection : Connection)
    (parameters : List Value) (table : Table) (condition : Option Resolved.Expr) (aggregate : Resolved.Aggregate)
    (name : String) (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query
      (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) []).Calm) :
    resolvedStepOutput none index connection parameters
      (.query (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) []) =
      if aggregate.fails (Resolved.EvalContext.bound parameters) ((Resolved.sourceRows table).filter fun row =>
          condition.all fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row))
        then .error ExecutionError.integerOverflow.primaryCode
        else Output.ofResults ((Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name).possibleResults
           (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table)) := by
  have found := Resolved.Query.source_first (connection.queryContext parameters
    (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) [])
    (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name)
    connection.state.database position table rfl present
  rw [resolvedStepOutput_query_source index connection parameters _ [] _ calm.readsClock (calm.firstUnknown _) found]
  dsimp only
  rw [Resolved.Query.aggregateOf_run_of_faultless _ _ _ _ _ calm.query_plain _ (calm.faultless_nil connection parameters)]
  simp only [calm.subqueries_plain, ↓reduceIte,
    Bool.false_eq_true, Resolved.Query.aggregateOf_bindWindow, Connection.queryContext_of_calm connection parameters _ calm,
    Resolved.Query.aggregateOf_filtered]
  rfl

/-- For every condition and aggregate whose expressions are calm ({name}`Resolved.Expr.Calm`) and every position, the
statement of the whole-table aggregate query of the first source of a table is calm
({name}`Resolved.Statement.Calm`): the first source of a table has no expression, so the expressions of the
statement are the condition and the operands of the aggregate. Proof sketch: list the expressions of the query. -/
theorem Resolved.Statement.Calm.aggregateOf_first (position : Nat) (condition : Option Resolved.Expr)
    (aggregate : Resolved.Aggregate) (name : String) (conditionCalm : ∀ expression ∈ condition.toList, expression.Calm)
    (operandsCalm : ∀ expression ∈ (Resolved.Output.aggregate aggregate).operands, expression.Calm) :
    (Resolved.Statement.query
      (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) []).Calm := by
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.expressions, Resolved.Query.keptExpressions,
    Resolved.Query.aggregateOf, Resolved.QuerySource.first, Resolved.QuerySource.expressions, List.mem_append,
    List.mem_flatMap, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at member
  simp only [Resolved.Output.scalars, List.map_nil, List.not_mem_nil, or_false] at member
  rcases member with (member | ⟨_, rfl, member | member⟩) | member
  · exact conditionCalm expression member
  · simp at member
  · simp at member
  · simp_all

end Belay.Sqlite.Model
