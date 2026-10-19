import Belay.Sqlite.Resolution.Resolve

set_option doc.verso true

/-! Writes leave the catalog unchanged: a successful resolution of INSERT, UPDATE or
DELETE returns the input catalog, and the resolved statement does not change a catalog
({name}`Belay.Sqlite.Resolved.Statement.applyCatalog`). {lit}`NamesSpec` uses these
lemmas for the unique-names rule, and {lit}`CatalogAgreement` for the catalog that
execution reaches. -/

namespace Belay.Sqlite

/-- For every successful resolution of INSERT, the catalog is unchanged and the resolved
statement applied to the input catalog gives the input catalog again
({name}`Resolved.Statement.applyCatalog`); the statement is not transaction control ({name}`Resolved.Statement.isControl`).
Proof sketch: every branch of the resolver returns the input catalog and a write or a
prepare error. -/
theorem resolveInsert_same (context : ResolveContext) (catalog after : Catalog) (index : Nat)
    (tableName : Identifier) (names : Option (List Identifier)) (rows : List (List Syntax.Expr))
    (conflicts : List Syntax.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (returning : List Syntax.ResultColumn)
    (statement : Resolved.Statement)
    (ok : resolveInsert context catalog index tableName names rows conflicts algorithm returning = .ok (statement, after)) :
    after = catalog ∧ statement.applyCatalog catalog = catalog ∧ statement.isControl = false := by
  unfold resolveInsert at ok
  simp only [prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact ⟨rfl, rfl, rfl⟩)
    | (cases ok)

/-- For every successful resolution of UPDATE, the catalog is unchanged and the resolved
statement applied to the input catalog gives the input catalog again
({name}`Resolved.Statement.applyCatalog`); the statement is not transaction control ({name}`Resolved.Statement.isControl`).
Proof sketch: every branch of the resolver returns the input catalog and a write or a
prepare error. -/
theorem resolveUpdate_same (context : ResolveContext) (catalog after : Catalog) (index : Nat)
    (tableName : Identifier) (assignments : List (Identifier × Syntax.Expr)) (filter : Option Syntax.Expr)
    (returning : List Syntax.ResultColumn)
    (statement : Resolved.Statement)
    (ok : resolveUpdate context catalog index tableName assignments filter returning = .ok (statement, after)) :
    after = catalog ∧ statement.applyCatalog catalog = catalog ∧ statement.isControl = false := by
  unfold resolveUpdate at ok
  simp only [prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact ⟨rfl, rfl, rfl⟩)
    | (cases ok)

/-- For every successful resolution of DELETE, the catalog is unchanged and the resolved
statement applied to the input catalog gives the input catalog again
({name}`Resolved.Statement.applyCatalog`); the statement is not transaction control ({name}`Resolved.Statement.isControl`).
Proof sketch: every branch of the resolver returns the input catalog and a write or a
prepare error. -/
theorem resolveDelete_same (context : ResolveContext) (catalog after : Catalog) (index : Nat)
    (tableName : Identifier) (filter : Option Syntax.Expr) (returning : List Syntax.ResultColumn)
    (statement : Resolved.Statement)
    (ok : resolveDelete context catalog index tableName filter returning = .ok (statement, after)) :
    after = catalog ∧ statement.applyCatalog catalog = catalog ∧ statement.isControl = false := by
  unfold resolveDelete at ok
  simp only [prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact ⟨rfl, rfl, rfl⟩)
    | (cases ok)

end Belay.Sqlite
