import Belay.Sqlite.Model.Resolution.Resolve

set_option doc.verso true

/-! Writes leave the catalog unchanged: a successful resolution of INSERT, UPDATE or
DELETE returns the input catalog, and the resolved statement does not change a catalog
({name}`Belay.Sqlite.Model.Resolved.Statement.applyCatalog`). {lit}`NamesSpec` uses these
lemmas for the unique-names rule, and {lit}`CatalogAgreement` for the catalog that
execution reaches. -/

namespace Belay.Sqlite.Model

/-- For every successful resolution of INSERT, the catalog is unchanged and the resolved
statement applied to the input catalog gives the input catalog again
({name}`Resolved.Statement.applyCatalog`); the statement is not transaction control ({name}`Resolved.Statement.isControl`).
Proof sketch: every branch of the resolver returns the input catalog and a write or a
prepare error. -/
theorem resolveInsert_same (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (names : Option (List Identifier)) (rows : List (List Syntax.Expr))
    (conflicts : List Syntax.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query) (shapes : SubqueryShapes)
    (statement : Resolved.Statement)
    (ok : resolveInsert context catalog tableName names rows conflicts algorithm returning subqueries shapes =
      .ok (statement, after)) :
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
theorem resolveUpdate_same (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (assignments : List (Identifier × Syntax.Expr)) (filter : Option Syntax.Expr)
    (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query) (shapes : SubqueryShapes)
    (statement : Resolved.Statement)
    (ok : resolveUpdate context catalog tableName assignments filter returning subqueries shapes =
      .ok (statement, after)) :
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
theorem resolveDelete_same (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (filter : Option Syntax.Expr) (returning : List Syntax.ResultColumn)
    (subqueries : List Resolved.Query) (shapes : SubqueryShapes) (statement : Resolved.Statement)
    (ok : resolveDelete context catalog tableName filter returning subqueries shapes = .ok (statement, after)) :
    after = catalog ∧ statement.applyCatalog catalog = catalog ∧ statement.isControl = false := by
  unfold resolveDelete at ok
  simp only [prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact ⟨rfl, rfl, rfl⟩)
    | (cases ok)

/-- For every write whose resolution with any subqueries and shapes keeps the catalog
({lit}`each`), every successful resolution of its subqueries and then of the write
({name}`resolveWriteSubqueries`) keeps it: the catalog is unchanged, the resolved statement
applied to the input catalog gives the input catalog again, and it is not transaction control.
Proof sketch: the other branches are a prepare error or a restriction. -/
theorem resolveWriteSubqueries_same {columnNames : List (Nat × List Identifier)} (context : ResolveContext) (catalog after : Catalog) (field : Nat)
    (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : List Resolved.Query → SubqueryShapes → StatementResolution) (statement : Resolved.Statement)
    (each : ∀ resolved shapes after statement, resolveWrite resolved shapes = .ok (statement, after) →
      after = catalog ∧ statement.applyCatalog catalog = catalog ∧ statement.isControl = false)
    (ok : resolveWriteSubqueries context catalog field tableName scopeOf subqueries resolveWrite columnNames =
      .ok (statement, after)) :
    after = catalog ∧ statement.applyCatalog catalog = catalog ∧ statement.isControl = false := by
  unfold resolveWriteSubqueries at ok
  simp only [prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact ⟨rfl, rfl, rfl⟩)
    | (cases ok)
    | (obtain h | ⟨rfl, error, rfl⟩ := resolveViewTarget_cases ok; exact each _ _ _ _ h; exact ⟨rfl, rfl, rfl⟩)
    | exact each _ _ _ _ ok

/-- For every write callback whose successful resolution keeps the catalog for every
query-index mapping, subquery list and shape: every successful resolution through
{name}`resolveCommonTableWrite` keeps the catalog, applying its statement leaves that catalog
unchanged, and its statement is not transaction control.
Proof sketch: expansion errors produce a prepare error or restriction; otherwise the ordinary
write-subquery resolver returns a statement covered by the given catalog fact. -/
theorem resolveCommonTableWrite_same (context : ResolveContext) (catalog after : Catalog) (field : Nat)
    (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : (Nat → Nat) → List Resolved.Query → SubqueryShapes → StatementResolution)
    (statement : Resolved.Statement)
    (each : ∀ index resolved shapes after statement, resolveWrite index resolved shapes = .ok (statement, after) →
      after = catalog ∧ statement.applyCatalog catalog = catalog ∧ statement.isControl = false)
    (ok : resolveCommonTableWrite context catalog field tableName scopeOf subqueries resolveWrite =
      .ok (statement, after)) :
    after = catalog ∧ statement.applyCatalog catalog = catalog ∧ statement.isControl = false := by
  unfold resolveCommonTableWrite at ok
  simp only [resolveWriteSubqueries, prepareError, restrict, issueResolution, Except.mapError] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact ⟨rfl, rfl, rfl⟩)
    | (cases ok)
    | (obtain h | ⟨rfl, error, rfl⟩ := resolveViewTarget_cases ok; exact each _ _ _ _ _ h; exact ⟨rfl, rfl, rfl⟩)
    | exact each _ _ _ _ _ ok
  all_goals
    rename_i found
    repeat' split at found
    all_goals first
      | (cases found; exact ⟨rfl, rfl, rfl⟩)
      | (cases found)
      | (obtain h | ⟨rfl, error, rfl⟩ := resolveViewTarget_cases found; exact each _ _ _ _ _ h; exact ⟨rfl, rfl, rfl⟩)
      | exact each _ _ _ _ _ found

end Belay.Sqlite.Model
