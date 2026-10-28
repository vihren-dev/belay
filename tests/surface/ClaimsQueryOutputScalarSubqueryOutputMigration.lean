import Belay.Sqlite.Model.ScalarSubqueryOutput

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite.Model

-- Original resolvedStepOutput_scalar_hasRows.
example (index : Nat) (connection : Connection) (parameters : List Value)
    (condition : Resolved.Expr) (position : Nat) (table : Table) (subCondition : Option Resolved.Expr)
    (value : Resolved.Expr) (names : List String)
    (present : connection.state.database.table position = some table)
    (noScalar : condition.any (· matches .subquery _) = false)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition [.scalar value] names]).Calm) :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition [.scalar value] names])).hasRows = true ↔
      Resolved.truthy (condition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.certain
          (Resolved.scalarRows (Resolved.EvalContext.bound parameters) subCondition value table)]) []) = true := by
  rw [resolvedStepOutput_scalar index connection parameters condition position table subCondition value names present noScalar calm]
  simp [Output.hasRows, apply_ite]

-- Original resolvedStepOutput_scalar_hasNoRows.
example (index : Nat) (connection : Connection) (parameters : List Value)
    (condition : Resolved.Expr) (position : Nat) (table : Table) (subCondition : Option Resolved.Expr)
    (value : Resolved.Expr) (names : List String)
    (present : connection.state.database.table position = some table)
    (noScalar : condition.any (· matches .subquery _) = false)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition [.scalar value] names]).Calm) :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition [.scalar value] names])).hasNoRows = true ↔
      Resolved.truthy (condition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.certain
          (Resolved.scalarRows (Resolved.EvalContext.bound parameters) subCondition value table)]) []) = false := by
  rw [resolvedStepOutput_scalar index connection parameters condition position table subCondition value names present noScalar calm]
  simp [Output.hasNoRows, apply_ite]

-- Original resolvedStepOutput_scalar_not_isError.
example (index : Nat) (connection : Connection) (parameters : List Value)
    (condition : Resolved.Expr) (position : Nat) (table : Table) (subCondition : Option Resolved.Expr)
    (value : Resolved.Expr) (names : List String)
    (present : connection.state.database.table position = some table)
    (noScalar : condition.any (· matches .subquery _) = false)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition [.scalar value] names]).Calm) :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition [.scalar value] names])).isError = false := by
  rw [resolvedStepOutput_scalar index connection parameters condition position table subCondition value names present noScalar calm]
  simp [Output.isError]

end Belay.Sqlite.Model
