import Belay.Sqlite.Model.Queries.Evaluation.TwoStateNotExistsExcept

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every statement {name}`Resolved.notExistsExcept` whose compound has the shape of
{name}`Resolved.Query.PlainExcept` and whose condition and columns are row-wise ({name}`Resolved.Expr.Rowwise`), the
statement is calm. Proof sketch: the
expressions of the statement are those of the main query ({lit}`NOT EXISTS` and the literal one), the compound (none)
and the two terms, which are row-wise and so calm. -/
theorem Resolved.notExistsExcept_calm (compound : Resolved.Query) (position : Nat) (condition : Resolved.Expr)
    (columns : List Resolved.Expr) (names : List String) (collations : List Collation)
    (shape : compound.PlainExcept 1 2 collations) (conditionOk : condition.Rowwise)
    (columnsOk : ∀ c ∈ columns, c.Rowwise) :
    (Resolved.notExistsExcept compound position condition columns names).Calm := by
  have rowwise1 := Resolved.Query.simple_expressions_rowwise
    [{ kind := .inner, source := .initialTable position, condition := none }] (some condition) columns names
    (by simp [Resolved.QuerySource.expressions]) (by simpa using conditionOk) columnsOk
  have rowwise2 := Resolved.Query.simple_expressions_rowwise [Resolved.QuerySource.first position] none columns names
    (by simp [Resolved.QuerySource.first, Resolved.QuerySource.expressions]) (by simp) columnsOk
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.notExistsExceptSubqueries,
    Resolved.Query.selectOneWhere_expressions, shape.expressions, List.mem_append, List.mem_cons,
    List.mem_nil_iff, or_false, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append] at member
  rcases member with (rfl | rfl) | member | member
  · simp [Resolved.Expr.Calm, Resolved.Expr.any, Resolved.Expr.isFallibleCall, Resolved.Expr.readsClockHere,
      Resolved.Expr.readsCounterHere]
  · simp [Resolved.Expr.Calm, Resolved.Expr.any, Resolved.Expr.isFallibleCall, Resolved.Expr.readsClockHere,
      Resolved.Expr.readsCounterHere]
  · exact (rowwise1 expression member).calm
  · exact (rowwise2 expression member).calm

end Belay.Sqlite.Model
