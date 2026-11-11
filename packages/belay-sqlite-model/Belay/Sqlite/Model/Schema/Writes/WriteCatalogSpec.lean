import Belay.Sqlite.Model.Schema.Dispatch.Resolve

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
  unfold resolveInsert resolveInsertTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact ⟨rfl, rfl, rfl⟩)
    | (cases ok)

/-- For every successful resolution of INSERT from a query, the catalog is unchanged and the resolved
statement is a prepare error, or an INSERT from a query without rules ({name}`Resolved.Statement.insertSelect`).
Proof sketch: every branch of the resolver returns the input catalog with a prepare error, a restriction,
which is not a success, or the INSERT from a query. -/
theorem resolveInsertQuery_form (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (names : Option (List Identifier)) (body : Syntax.SelectBody)
    (conflicts : List Syntax.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (returning : List Syntax.ResultColumn) (statement : Resolved.Statement)
    (ok : (resolveInsertQueryTraced context catalog tableName names body conflicts algorithm returning).drop =
      .ok (statement, after)) :
    after = catalog ∧ ((∃ error, statement = .prepareError error) ∨
      ∃ table cells query clauses returning algorithm subqueries,
        statement = .insertSelect table cells query clauses returning algorithm subqueries none) := by
  unfold resolveInsertQueryTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact ⟨rfl, .inl ⟨_, rfl⟩⟩)
    | (cases ok; exact ⟨rfl, .inr ⟨_, _, _, _, _, _, _, rfl⟩⟩)
    | (cases ok)
    | (obtain h | ⟨rfl, error, rfl⟩ := resolveViewTarget_cases
          (show resolveViewTarget context catalog tableName (resolveViewModify catalog tableName) =
            .ok (statement, after) from ok)
       · simp only [resolveViewModify, prepareError] at h
         cases h
         exact ⟨rfl, .inl ⟨_, rfl⟩⟩
       · exact ⟨rfl, .inl ⟨_, rfl⟩⟩)

/-- For every successful resolution of INSERT from a query, the catalog is unchanged and the resolved
statement applied to the input catalog gives the input catalog again; the statement is not transaction
control. Proof sketch: the statement is a prepare error or an INSERT from a query ({name}`resolveInsertQuery_form`), and both leave the catalog. -/
theorem resolveInsertQuery_same (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (names : Option (List Identifier)) (body : Syntax.SelectBody)
    (conflicts : List Syntax.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (returning : List Syntax.ResultColumn) (statement : Resolved.Statement)
    (ok : (resolveInsertQueryTraced context catalog tableName names body conflicts algorithm returning).drop =
      .ok (statement, after)) :
    after = catalog ∧ statement.applyCatalog catalog = catalog ∧ statement.isControl = false := by
  obtain ⟨rfl, ⟨error, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩⟩ := resolveInsertQuery_form _ _ _ _ _ _ _ _ _ _ ok <;>
    exact ⟨rfl, rfl, rfl⟩

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
  unfold resolveUpdate resolveUpdateTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
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
  unfold resolveDelete resolveDeleteTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact ⟨rfl, rfl, rfl⟩)
    | (cases ok)

end Belay.Sqlite.Model
