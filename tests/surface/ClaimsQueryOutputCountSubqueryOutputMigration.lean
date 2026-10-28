import Belay.Sqlite.Model.CountSubqueryOutput

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite.Model

-- Original resolvedStepOutput_count_hasRows.
example (index : Nat) (connection : Connection) (parameters : List Value)
    (condition : Resolved.Expr) (position : Nat) (table : Table) (subCondition : Option Resolved.Expr) (name : String)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition name]).Calm) :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition name])).hasRows = true ↔
      Resolved.truthy (condition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.count (Resolved.countMatching (Resolved.EvalContext.bound parameters) subCondition table)]) []) = true := by
  rw [resolvedStepOutput_count index connection parameters condition position table subCondition name present calm]
  simp [Output.hasRows, apply_ite]

-- Original resolvedStepOutput_count_hasNoRows.
example (index : Nat) (connection : Connection) (parameters : List Value)
    (condition : Resolved.Expr) (position : Nat) (table : Table) (subCondition : Option Resolved.Expr) (name : String)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition name]).Calm) :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition name])).hasNoRows = true ↔
      Resolved.truthy (condition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.count (Resolved.countMatching (Resolved.EvalContext.bound parameters) subCondition table)]) []) = false := by
  rw [resolvedStepOutput_count index connection parameters condition position table subCondition name present calm]
  simp [Output.hasNoRows, apply_ite]

-- Original resolvedStepOutput_count_not_isError.
example (index : Nat) (connection : Connection) (parameters : List Value)
    (condition : Resolved.Expr) (position : Nat) (table : Table) (subCondition : Option Resolved.Expr) (name : String)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition name]).Calm) :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition name])).isError = false := by
  rw [resolvedStepOutput_count index connection parameters condition position table subCondition name present calm]
  simp [Output.isError]

end Belay.Sqlite.Model
