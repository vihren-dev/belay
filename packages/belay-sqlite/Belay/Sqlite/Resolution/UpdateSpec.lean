import Belay.Sqlite.Resolution.Resolve

set_option doc.verso true

/-! The prepare-error rule for UPDATE. See {lit}`PrepareSpec.lean` for the rule and
its references. -/

namespace Belay.Sqlite

/-- For every UPDATE whose resolution is a prepare error that names a catalog object:
the error is {lit}`no such table` for the statement's table, no table has the folded
name, and the catalog is unchanged. Proof sketch: split every branch of the
resolver; after the table lookup, the assignments, the filter and the
{lit}`RETURNING` columns give errors that name no catalog object. -/
theorem resolveUpdate_named (context : ResolveContext) (catalog after : Catalog) (index : Nat)
    (tableName : String) (assignments : List (String × Syntax.Expr)) (filter : Option Syntax.Expr)
    (returning : List Syntax.ResultColumn)
    (error : PrepareError) (named : ∀ cause, error ≠ .expression cause)
    (ok : resolveUpdate context catalog index tableName assignments filter returning = .ok (.prepareError error, after)) :
    error = .noSuchTable tableName ∧ catalog.findTable tableName = none ∧ after = catalog := by
  unfold resolveUpdate at ok
  simp only [prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals (try (cases ok; done))
  all_goals cases ok
  all_goals first
    | exact absurd rfl (named _)
    | (simp_all; done)

/-- For every UPDATE: when no table has the folded name, the resolution is
{lit}`no such table`, and the catalog is unchanged. -/
theorem resolveUpdate_missing (context : ResolveContext) (catalog : Catalog) (index : Nat)
    (tableName : String) (assignments : List (String × Syntax.Expr)) (filter : Option Syntax.Expr)
    (returning : List Syntax.ResultColumn)
    (missing : catalog.findTable tableName = none) :
    resolveUpdate context catalog index tableName assignments filter returning =
      .ok (.prepareError (.noSuchTable tableName), catalog) := by
  unfold resolveUpdate
  simp [missing, prepareError]

end Belay.Sqlite
