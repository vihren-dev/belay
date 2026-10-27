import Belay.Sqlite.Model.ResolveStatementLink
import Belay.Sqlite.Model.StatementSingleton

set_option doc.verso true

/-! The first part of the claim that only INSERT from a query can have more than one possible execution (ADR 0019, D4,
amended 2026-10-25): the resolvers of CREATE TABLE, CREATE INDEX, CREATE TRIGGER, INSERT, UPDATE and DELETE give
a statement that is no INSERT from a query without rules
({name}`Belay.Sqlite.Model.Resolved.Statement.fromQuery`). The other resolvers are in
{lit}`Belay.Sqlite.Model.ResolveStatementSingleOthers`, and the claim for every statement in
{lit}`Belay.Sqlite.Model.ResolveStatementSingle`. -/

namespace Belay.Sqlite.Model

/-- For every successful resolution of CREATE TABLE, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of CREATE TABLE. -/
theorem resolveCreateTable_single (context : ResolveContext) (catalog after : Catalog)
    (name : Identifier) (columns : List Syntax.ColumnDefinition) (constraints : List Syntax.TableConstraint)
    (options : Syntax.TableOptions) (statement : Resolved.Statement)
    (ok : resolveCreateTable context catalog name columns constraints options = .ok (statement, after)) :
    statement.fromQuery = false := by
  unfold resolveCreateTable at ok
  simp only [issueResolution, prepareError, restrict] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of CREATE INDEX, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of CREATE INDEX. -/
theorem resolveCreateIndex_single (context : ResolveContext) (catalog after : Catalog)
    (name : Identifier) (unique : Bool) (tableName : Identifier) (terms : List Syntax.OrderTerm)
    (filter : Option Syntax.Expr) (statement : Resolved.Statement)
    (ok : resolveCreateIndex context catalog name unique tableName terms filter = .ok (statement, after)) :
    statement.fromQuery = false := by
  unfold resolveCreateIndex at ok
  simp only [issueResolution, prepareError, restrict] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of CREATE TRIGGER, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of CREATE TRIGGER. -/
theorem resolveCreateTrigger_single (catalog after : Catalog) (name : Identifier)
    (ifNotExists : Bool) (trigger : CatalogTrigger) (statement : Resolved.Statement)
    (ok : resolveCreateTrigger catalog name ifNotExists trigger = .ok (statement, after)) :
    statement.fromQuery = false := by
  unfold resolveCreateTrigger at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of INSERT, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of INSERT. -/
theorem resolveInsert_single (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (names : Option (List Identifier)) (rows : List (List Syntax.Expr))
    (conflicts : List Syntax.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query) (shapes : SubqueryShapes)
    (statement : Resolved.Statement)
    (ok : resolveInsert context catalog tableName names rows conflicts algorithm returning subqueries shapes =
      .ok (statement, after)) : statement.fromQuery = false := by
  unfold resolveInsert resolveInsertTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of UPDATE, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of UPDATE. -/
theorem resolveUpdate_single (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (assignments : List (Identifier × Syntax.Expr)) (filter : Option Syntax.Expr)
    (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query) (shapes : SubqueryShapes)
    (statement : Resolved.Statement)
    (ok : resolveUpdate context catalog tableName assignments filter returning subqueries shapes =
      .ok (statement, after)) : statement.fromQuery = false := by
  unfold resolveUpdate resolveUpdateTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of DELETE, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of DELETE. -/
theorem resolveDelete_single (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (filter : Option Syntax.Expr) (returning : List Syntax.ResultColumn)
    (subqueries : List Resolved.Query) (shapes : SubqueryShapes) (statement : Resolved.Statement)
    (ok : resolveDelete context catalog tableName filter returning subqueries shapes = .ok (statement, after)) :
    statement.fromQuery = false := by
  unfold resolveDelete resolveDeleteTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

end Belay.Sqlite.Model
