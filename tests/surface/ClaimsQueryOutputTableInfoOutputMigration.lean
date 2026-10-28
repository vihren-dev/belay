import Belay.Sqlite.Model.TableInfoOutput

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite.Model

-- Original resolvedStepOutput_simplePragma_hasRows.
example (index : Nat) (connection : Connection) (parameters : List Value)
    (width : Nat) (rows : List (List Value)) (condition : Option Resolved.Expr) (columns : List Resolved.Output)
    (names : List String)
    (calm : (Resolved.Statement.query (Resolved.Query.simple [Resolved.QuerySource.pragma (.fixed width rows)] condition
      columns names) []).Calm) :
    (resolvedStepOutput none index connection parameters
      (.query (Resolved.Query.simple [Resolved.QuerySource.pragma (.fixed width rows)] condition columns names) [])).hasRows = true ↔
      ∃ row ∈ rows, condition.all
        (fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) = true := by
  rw [resolvedStepOutput_simplePragma index connection parameters width rows condition columns names calm]
  simp only [Output.hasRows, Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq,
    Resolved.normalForm_eq_nil, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    Classical.not_forall, Classical.not_not, exists_prop]

-- Original resolvedStepOutput_simplePragma_hasNoRows.
example (index : Nat) (connection : Connection) (parameters : List Value)
    (width : Nat) (rows : List (List Value)) (condition : Option Resolved.Expr) (columns : List Resolved.Output)
    (names : List String)
    (calm : (Resolved.Statement.query (Resolved.Query.simple [Resolved.QuerySource.pragma (.fixed width rows)] condition
      columns names) []).Calm) :
    (resolvedStepOutput none index connection parameters
      (.query (Resolved.Query.simple [Resolved.QuerySource.pragma (.fixed width rows)] condition columns names) [])).hasNoRows = true ↔
      ∀ row ∈ rows, condition.all
        (fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) = false := by
  rw [resolvedStepOutput_simplePragma index connection parameters width rows condition columns names calm]
  simp only [Output.hasNoRows, List.isEmpty_iff, Resolved.normalForm_eq_nil,
    List.map_eq_nil_iff, List.filter_eq_nil_iff, Bool.not_eq_true]

-- Original resolvedStepOutput_simplePragma_not_isError.
example (index : Nat) (connection : Connection) (parameters : List Value)
    (width : Nat) (rows : List (List Value)) (condition : Option Resolved.Expr) (columns : List Resolved.Output)
    (names : List String)
    (calm : (Resolved.Statement.query (Resolved.Query.simple [Resolved.QuerySource.pragma (.fixed width rows)] condition
      columns names) []).Calm) :
    (resolvedStepOutput none index connection parameters
      (.query (Resolved.Query.simple [Resolved.QuerySource.pragma (.fixed width rows)] condition columns names) [])).isError = false := by
  rw [resolvedStepOutput_simplePragma index connection parameters width rows condition columns names calm]
  rfl

end Belay.Sqlite.Model
