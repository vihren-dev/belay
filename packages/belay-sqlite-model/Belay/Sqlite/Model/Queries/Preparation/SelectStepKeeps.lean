import Belay.Sqlite.Model.Queries.Select.SelectResolution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every successful resolution of a SELECT: the resolved statement is a query or a prepare
error. Proof sketch: every successful branch of the resolver returns one of the two
({name}`resolveSelect_same` reads the same branches). -/
theorem resolveSelect_shape (context : ResolveContext) (catalog after : Catalog)
    (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) (statement : Resolved.Statement)
    (ok : resolveSelect context catalog query subqueries = .ok (statement, after)) :
    (∃ resolvedQuery resolvedSubqueries, statement = .query resolvedQuery resolvedSubqueries) ∨
      ∃ error, statement = .prepareError error := by
  unfold resolveSelect resolveSelectTraced at ok
  dsimp only [Traced.drop] at ok
  simp only [prepareError, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact Or.inl ⟨_, _, rfl⟩)
    | (cases ok; exact Or.inr ⟨_, rfl⟩)
    | (cases ok)

end Belay.Sqlite.Model
