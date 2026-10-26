import Belay.Sqlite.Model.ResolveStatementPragmaLink
import Belay.Sqlite.Model.ResolveStatementLink
import Belay.Sqlite.Model.StatementSingleton

set_option doc.verso true

/-! Which statements can have more than one possible execution (ADR 0019, D4, amended 2026-10-25). Only
the resolver of INSERT from a query gives a statement without rules that is an INSERT from a query
({name}`Belay.Sqlite.Model.Resolved.Statement.fromQuery`); every other resolver gives a statement of
another form. So a script whose statements are no INSERT from a query has one execution for each of them. -/

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

/-- For every write resolution whose statements are no INSERT from a query without rules ({lit}`each`), every
successful resolution of its subqueries and then of the write ({name}`resolveWriteSubqueries`) is no INSERT from a
query without rules. Proof sketch: the other branches are a prepare error or a restriction. -/
theorem resolveWriteSubqueries_single {columnNames : List (Nat × List Identifier)} (context : ResolveContext) (catalog after : Catalog)
    (field : Nat) (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : List Resolved.Query → SubqueryShapes → StatementResolution) (statement : Resolved.Statement)
    (each : ∀ resolved shapes after statement, resolveWrite resolved shapes = .ok (statement, after) →
      statement.fromQuery = false)
    (ok : resolveWriteSubqueries context catalog field tableName scopeOf subqueries resolveWrite columnNames =
      .ok (statement, after)) : statement.fromQuery = false := by
  unfold resolveWriteSubqueries resolveWriteSubqueriesTraced resolveViewTargetTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)
    | (obtain h | ⟨rfl, error, rfl⟩ := resolveViewTarget_cases ok; exact each _ _ _ _ h; rfl)
    | exact each _ _ _ _ ok

/-- For every write resolution whose statements are no INSERT from a query without rules for every copied query
mapping, successful WITH expansion and write resolution also give no INSERT from a query without rules. Proof
sketch: the wrapper's other successful branches are prepare errors; the write branch has the assumed form
regardless of its copied queries and explicit column names. -/
theorem resolveCommonTableWrite_single (context : ResolveContext) (catalog after : Catalog)
    (field : Nat) (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : (Nat → Nat) → List Resolved.Query → SubqueryShapes → StatementResolution)
    (statement : Resolved.Statement)
    (each : ∀ index resolved shapes after statement, resolveWrite index resolved shapes = .ok (statement, after) →
      statement.fromQuery = false)
    (ok : resolveCommonTableWrite context catalog field tableName scopeOf subqueries resolveWrite =
      .ok (statement, after)) : statement.fromQuery = false := by
  unfold resolveCommonTableWrite resolveCommonTableWriteTraced resolveViewTargetTraced at ok
  simp only [resolveWriteSubqueriesTraced, traced_drop, prepareError, restrict, issueResolution, Except.mapError] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)
    | (obtain h | ⟨rfl, error, rfl⟩ := resolveViewTarget_cases ok; exact each _ _ _ _ _ h; rfl)
    | exact each _ _ _ _ _ ok
  all_goals
    rename_i found
    repeat' split at found
    all_goals first
      | (cases found; rfl)
      | (cases found)
      | (obtain h | ⟨rfl, error, rfl⟩ := resolveViewTarget_cases found; exact each _ _ _ _ _ h; rfl)
      | exact each _ _ _ _ _ found

/-- For every statement that is no INSERT from a query without rules and every rules: the write with the rules
({name}`Resolved.Statement.withRules`) is no INSERT from a query without rules. Proof sketch: the rules
change only the rules of a write, and a write with rules is not an INSERT without rules. -/
theorem Resolved.Statement.fromQuery_withRules {statement : Resolved.Statement} (rules : Resolved.WriteRules)
    (single : statement.fromQuery = false) : (statement.withRules rules).fromQuery = false := by
  cases statement <;> first | exact single | rfl

/-- For every context, state, resolution and result of {name}`ResolveState.withWrite`: if every statement of
the resolution is no INSERT from a query without rules, neither is the resolved statement of the result. Proof
sketch: each branch gives a prepare error, the statement, or the statement with rules
({name}`Resolved.Statement.fromQuery_withRules`). -/
theorem ResolveState.withWrite_single {context : ResolveContext} {state next : ResolveState}
    {result : StatementResolution} {resolved : Resolved.Statement}
    (ok : state.withWrite context result = .ok (resolved, next))
    (each : ∀ statement catalog, result = .ok (statement, catalog) → statement.fromQuery = false) :
    resolved.fromQuery = false := by
  unfold ResolveState.withWrite ResolveState.withCatalog at ok
  rcases result with _ | ⟨statement, catalog⟩
  · cases ok
  · simp only [Except.map, bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; rfl)
      | (cases ok; exact each _ _ rfl)
      | (cases ok; exact Resolved.Statement.fromQuery_withRules _ (each _ _ rfl))
      | cases ok

/-- Whether the statement is INSERT from a query ({lit}`INSERT INTO t SELECT ...`), the one syntax whose
resolved statement can be an INSERT from a query without rules. -/
def Syntax.Statement.isInsertSelect : Syntax.Statement → Bool
  | .insertSelect .. => true
  | _ => false

/-- For every context, state, statement that is no INSERT from a query and resolution: the resolved statement is
no INSERT from a query without rules ({name}`Resolved.Statement.fromQuery`), so its run has no alternative
execution. Plain words: only a statement that is written as INSERT from a query can have more than one possible
execution. Proof sketch: a case for each statement, with the lemma of its resolver ({name}`resolveCreateTable_single`
and the lemmas of the other resolvers); a write that checks keys keeps the claim
({name}`ResolveState.withWrite_single`). -/
theorem resolveStatement_single (context : ResolveContext) (state next : ResolveState)
    (statement : Syntax.Statement) (resolved : Resolved.Statement) (notQuery : statement.isInsertSelect = false)
    (ok : resolveStatement context state statement = .ok (resolved, next)) : resolved.fromQuery = false := by
  have plain : ∀ result, state.withCatalog result = .ok (resolved, next) →
      (∀ statement after, result = .ok (statement, after) → statement.fromQuery = false) →
      resolved.fromQuery = false := by
    intro result ok each
    rcases result with _ | ⟨statement, after⟩
    · cases ok
    · simp only [ResolveState.withCatalog, Except.map, Except.ok.injEq, Prod.mk.injEq] at ok
      obtain ⟨rfl, _⟩ := ok
      exact each _ _ rfl
  cases statement
  all_goals simp only [statement_arms] at ok
  case begin => cases ok; rfl
  case commit => cases ok; rfl
  case rollback => cases ok; rfl
  case createTable => exact plain _ ok fun _ _ found => resolveCreateTable_single _ _ _ _ _ _ _ _ found
  case createView => exact plain _ ok fun _ _ found => resolveCreateView_single _ _ _ _ _ _ found
  case createIndex => exact plain _ ok fun _ _ found => resolveCreateIndex_single _ _ _ _ _ _ _ _ _ found
  case addColumn => exact plain _ ok fun _ _ found => resolveAddColumn_single _ _ _ _ _ _ _ found
  case dropTable => exact ResolveState.withWrite_single ok fun _ _ found => resolveDropTable_single _ _ _ found
  case dropView => exact plain _ ok fun _ _ found => resolveDropView_single _ _ _ found
  case dropIndex => exact plain _ ok fun _ _ found => resolveDropIndex_single _ _ _ found
  case createTrigger => exact plain _ ok fun _ _ found => resolveCreateTrigger_single _ _ _ _ _ _ found
  case dropTrigger => exact plain _ ok fun _ _ found => resolveDropTrigger_single _ _ _ found
  case insert =>
    exact ResolveState.withWrite_single ok fun _ _ found => resolveCommonTableWrite_single _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveInsert_single _ _ _ _ _ _ _ _ _ _ _ _ h) found
  case insertSelect => simp [Syntax.Statement.isInsertSelect] at notQuery
  case update =>
    exact ResolveState.withWrite_single ok fun _ _ found => resolveCommonTableWrite_single _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveUpdate_single _ _ _ _ _ _ _ _ _ _ h) found
  case delete =>
    exact ResolveState.withWrite_single ok fun _ _ found => resolveCommonTableWrite_single _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveDelete_single _ _ _ _ _ _ _ _ _ h) found
  case pragma => exact resolveStatementPragma_single ok
  case select => exact plain _ ok fun _ _ found => resolveSelect_single _ _ _ _ _ _ found

end Belay.Sqlite.Model
