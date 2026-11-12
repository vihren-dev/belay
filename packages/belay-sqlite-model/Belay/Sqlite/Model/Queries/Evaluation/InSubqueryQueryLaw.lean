import Belay.Sqlite.Model.Queries.Evaluation.OneTableStatementOutput

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The expressions of the subquery {lit}`SELECT c FROM u` of an {lit}`IN` test are calm
({name}`Resolved.Expr.Calm`). Proof sketch: the one expression is a column ({name}`Resolved.Expr.calm_column`). -/
theorem Resolved.Query.inColumn_calm (table outer column : Nat) (names : List String) :
    ∀ expression ∈ (Resolved.Query.oneTable table outer none [.column (outer + column)] names).expressions,
      expression.Calm := by
  intro expression member
  rw [Resolved.Query.oneTable_expressions] at member
  simp only [Option.toList_none, List.nil_append, List.mem_singleton] at member
  subst member
  exact Resolved.Expr.calm_column _

/-- The expressions of the correlated subquery {lit}`SELECT 1 FROM u WHERE u.c = x` are calm. Proof sketch: they are a
comparison of two columns ({name}`Resolved.Expr.calm_compare`) and a literal. -/
theorem Resolved.Query.equalsColumn_calm (table outer column key : Nat) (affinity : Option Affinity)
    (collation : Collation) (names : List String) :
    ∀ expression ∈ (Resolved.Query.oneTable table outer
      (some (.compare .eq affinity (.column (outer + column)) (.column key) collation)) [.literal (.integer 1)]
      names).expressions, expression.Calm := by
  intro expression member
  rw [Resolved.Query.oneTable_expressions] at member
  simp only [Option.toList_some, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with rfl | rfl
  · exact (Resolved.Expr.calm_compare ..).mpr ⟨Resolved.Expr.calm_column _, Resolved.Expr.calm_column _⟩
  · exact Resolved.Expr.calm_literal _

end Belay.Sqlite.Model
