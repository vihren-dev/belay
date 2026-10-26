import Belay.Sqlite.Model.Resolution.Resolve

set_option doc.verso true

/-! The prepare-error rule for UPDATE. See {lit}`PrepareSpec.lean` for the rule and
its references. -/

namespace Belay.Sqlite.Model

/-- For every UPDATE, with any subqueries and shapes, whose resolution is a prepare error that names a catalog object:
the error is {lit}`no such table` for the statement's table, and no table has the folded
name, or it is {lit}`cannot modify %s because it is a view`; the catalog is unchanged. Proof sketch: split every branch of the
resolver; after the table lookup, the assignments, the filter and the
{lit}`RETURNING` columns give errors that name no catalog object. -/
theorem resolveUpdate_named (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (assignments : List (Identifier × Syntax.Expr)) (filter : Option Syntax.Expr)
    (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query) (shapes : SubqueryShapes)
    (error : PrepareError) (named : ∀ cause, error ≠ .expression cause)
    (ok : resolveUpdate context catalog tableName assignments filter returning subqueries shapes =
      .ok (.prepareError error, after)) :
    ((error = .noSuchTable tableName ∧ catalog.findTable tableName = none) ∨ ∃ name, error = .viewModify name) ∧
      after = catalog := by
  unfold resolveUpdate resolveUpdateTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals (try (cases ok; done))
  all_goals cases ok
  all_goals first
    | exact absurd rfl (named _)
    | exact ⟨.inr ⟨_, rfl⟩, rfl⟩
    | (simp_all; done)

/-- For every UPDATE, with any subqueries and shapes: when no table or view has the folded name, the resolution is
{lit}`no such table`, and the catalog is unchanged. -/
theorem resolveUpdate_missing (context : ResolveContext) (catalog : Catalog)
    (tableName : Identifier) (assignments : List (Identifier × Syntax.Expr)) (filter : Option Syntax.Expr)
    (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query) (shapes : SubqueryShapes)
    (missing : catalog.findTable tableName = none)
    (notView : catalog.findView tableName = none) :
    resolveUpdate context catalog tableName assignments filter returning subqueries shapes =
      .ok (.prepareError (.noSuchTable tableName), catalog) := by
  unfold resolveUpdate resolveUpdateTraced
  simp [missing, notView, prepareError, traced_drop]

end Belay.Sqlite.Model
