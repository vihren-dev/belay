import Belay.Sqlite.Model.ExistsSubqueryOutput

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite.Model

-- Original resolvedStepOutput_exists_hasRows.
example (index position : Nat) (connection : Connection) (parameters : List Value)
    (table : Table) (condition : Option Resolved.Expr) (columns : List Resolved.Output) (names : List String)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere (.exists 0))
      [Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names]).Calm) :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere (.exists 0))
      [Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names])).hasRows = true ↔
      ∃ row ∈ Resolved.sourceRows table, condition.all
        (fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) = true := by
  rw [resolvedStepOutput_exists index position connection parameters table condition columns names present calm]
  simp [Output.hasRows, apply_ite, List.any_eq_true]

-- Original resolvedStepOutput_exists_hasNoRows.
example (index position : Nat) (connection : Connection) (parameters : List Value)
    (table : Table) (condition : Option Resolved.Expr) (columns : List Resolved.Output) (names : List String)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere (.exists 0))
      [Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names]).Calm) :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere (.exists 0))
      [Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names])).hasNoRows = true ↔
      ∀ row ∈ Resolved.sourceRows table, condition.all
        (fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) = false := by
  rw [resolvedStepOutput_exists index position connection parameters table condition columns names present calm]
  simp [Output.hasNoRows, apply_ite, List.any_eq_true]

-- Original resolvedStepOutput_exists_not_isError.
example (index position : Nat) (connection : Connection) (parameters : List Value)
    (table : Table) (condition : Option Resolved.Expr) (columns : List Resolved.Output) (names : List String)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere (.exists 0))
      [Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names]).Calm) :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere (.exists 0))
      [Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names])).isError = false := by
  rw [resolvedStepOutput_exists index position connection parameters table condition columns names present calm]
  simp [Output.isError]

end Belay.Sqlite.Model
