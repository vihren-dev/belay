import Belay.Sqlite.Model.ResolveStatementPragmaLink
import Belay.Sqlite.Model.ResolveStatementSingleWrites

set_option doc.verso true

/-! The second part of the claim that only INSERT from a query can have more than one possible execution (ADR 0019,
D4, amended 2026-10-25): the resolvers of SELECT, CREATE VIEW, ADD COLUMN, the DROP statements and the pragmas give a
statement that is no INSERT from a query without rules
({name}`Belay.Sqlite.Model.Resolved.Statement.fromQuery`). -/

namespace Belay.Sqlite.Model

/-- For every successful resolution of SELECT, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of SELECT. -/
theorem resolveSelect_single (context : ResolveContext) (catalog after : Catalog)
    (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) (statement : Resolved.Statement)
    (ok : resolveSelect context catalog query subqueries = .ok (statement, after)) :
    statement.fromQuery = false := by
  unfold resolveSelect resolveSelectTraced at ok
  dsimp only [Traced.drop] at ok
  simp only [prepareError, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of CREATE VIEW, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of CREATE VIEW. -/
theorem resolveCreateView_single (catalog after : Catalog) (name : Identifier)
    (ifNotExists : Bool) (view : CatalogView) (statement : Resolved.Statement)
    (ok : resolveCreateView catalog name ifNotExists view = .ok (statement, after)) :
    statement.fromQuery = false := by
  unfold resolveCreateView at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of ADD COLUMN, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of ADD COLUMN. -/
theorem resolveAddColumn_single (context : ResolveContext) (enforced : Bool) (catalog after : Catalog)
    (tableName : Identifier) (definition : Syntax.ColumnDefinition) (statement : Resolved.Statement)
    (ok : resolveAddColumn context catalog enforced tableName definition = .ok (statement, after)) :
    statement.fromQuery = false := by
  unfold resolveAddColumn at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of DROP TABLE, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of DROP TABLE. -/
theorem resolveDropTable_single {catalog after : Catalog} (name : Identifier)
    (ifExists : Bool) (statement : Resolved.Statement)
    (ok : resolveDropTable catalog name ifExists = .ok (statement, after)) : statement.fromQuery = false := by
  unfold resolveDropTable at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of DROP INDEX, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of DROP INDEX. -/
theorem resolveDropIndex_single {catalog after : Catalog} (name : Identifier)
    (ifExists : Bool) (statement : Resolved.Statement)
    (ok : resolveDropIndex catalog name ifExists = .ok (statement, after)) : statement.fromQuery = false := by
  unfold resolveDropIndex at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of DROP TRIGGER, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of DROP TRIGGER. -/
theorem resolveDropTrigger_single {catalog after : Catalog} (name : Identifier)
    (ifExists : Bool) (statement : Resolved.Statement)
    (ok : resolveDropTrigger catalog name ifExists = .ok (statement, after)) : statement.fromQuery = false := by
  unfold resolveDropTrigger at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of DROP VIEW, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of DROP VIEW. -/
theorem resolveDropView_single {catalog after : Catalog} (name : Identifier)
    (ifExists : Bool) (statement : Resolved.Statement)
    (ok : resolveDropView catalog name ifExists = .ok (statement, after)) : statement.fromQuery = false := by
  unfold resolveDropView at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of a pragma ({name}`resolvePragma`), the resolved statement is no INSERT
from a query without rules. Proof sketch: every branch of the resolver gives a setting, a query or a prepare
error. -/
theorem resolvePragma_single {state next : ResolveState} {pragma : Syntax.Pragma}
    {resolved : Resolved.Statement} (ok : resolvePragma state pragma = .ok (resolved, next)) :
    resolved.fromQuery = false := by
  unfold resolvePragma at ok
  repeat' split at ok
  all_goals first | (cases ok; rfl) | (cases ok)

/-- For every successful resolution of a pragma statement ({name}`resolveStatementPragma`), the resolved
statement is no INSERT from a query without rules. Proof sketch: a view branch is a query or a prepare error;
every other pragma is {name}`resolvePragma_single`. -/
theorem resolveStatementPragma_single {context : ResolveContext} {state next : ResolveState}
    {pragma : Syntax.Pragma} {resolved : Resolved.Statement}
    (ok : resolveStatementPragma context state pragma = .ok (resolved, next)) :
    resolved.fromQuery = false := by
  unfold resolveStatementPragma at ok
  split at ok
  · rename_i table
    split at ok
    · unfold resolveViewTableInfo at ok
      cases read : viewColumns context state.catalog table with
      | ok columns =>
        rw [read] at ok
        cases ok
        rfl
      | error issue =>
        rw [read] at ok
        cases issue with
        | noSuchTable name =>
          simp only [readIssueResolution, prepareError, Except.map] at ok
          cases ok
          rfl
        | value inner =>
          cases inner <;> simp only [readIssueResolution, issueResolution, prepareError, restrict, Except.map] at ok
          · cases ok
            rfl
          · cases ok
    · exact resolvePragma_single ok
  all_goals exact resolvePragma_single ok

end Belay.Sqlite.Model
