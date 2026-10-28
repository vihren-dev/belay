import Belay.Sqlite.Model.DuplicateKeyOutput

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite.Model

-- Original resolvedStepOutput_notExists_duplicateKeys_hasRows.
example (index position : Nat) (connection : Connection)
    (parameters : List Value) (table : Table) (filter : Option Resolved.Expr) (column : Resolved.Expr) (name : String) (key : Resolved.Expr)
    (collation : Collation)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere (.not (.exists 0)))
      [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation]).Calm) :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere (.not (.exists 0)))
      [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation])).hasRows = true ↔
      ∀ group ∈ Resolved.groups (Resolved.EvalContext.bound parameters) [(key, collation)]
        (Resolved.keptRows (Resolved.EvalContext.bound parameters) filter (Resolved.sourceRows table)),
        group.length ≤ 1 := by
  rw [resolvedStepOutput_notExists_duplicateKeys index position connection parameters table filter column name key collation present calm]
  simp [Output.hasRows, apply_ite, List.all_eq_true]

-- Original resolvedStepOutput_notExists_duplicateKeys_hasNoRows.
example (index position : Nat) (connection : Connection)
    (parameters : List Value) (table : Table) (filter : Option Resolved.Expr) (column : Resolved.Expr) (name : String) (key : Resolved.Expr)
    (collation : Collation)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere (.not (.exists 0)))
      [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation]).Calm) :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere (.not (.exists 0)))
      [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation])).hasNoRows = true ↔
      ∃ group ∈ Resolved.groups (Resolved.EvalContext.bound parameters) [(key, collation)]
        (Resolved.keptRows (Resolved.EvalContext.bound parameters) filter (Resolved.sourceRows table)),
        1 < group.length := by
  rw [resolvedStepOutput_notExists_duplicateKeys index position connection parameters table filter column name key collation present calm]
  simp [Output.hasNoRows, apply_ite, List.all_eq_true, Nat.not_le]

-- Original resolvedStepOutput_notExists_duplicateKeys_not_isError.
example (index position : Nat) (connection : Connection)
    (parameters : List Value) (table : Table) (filter : Option Resolved.Expr) (column : Resolved.Expr) (name : String) (key : Resolved.Expr)
    (collation : Collation)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere (.not (.exists 0)))
      [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation]).Calm) :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere (.not (.exists 0)))
      [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation])).isError = false := by
  rw [resolvedStepOutput_notExists_duplicateKeys index position connection parameters table filter column name key collation present calm]
  simp [Output.isError]

end Belay.Sqlite.Model
