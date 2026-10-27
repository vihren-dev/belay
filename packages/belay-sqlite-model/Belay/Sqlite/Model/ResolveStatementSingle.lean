import Belay.Sqlite.Model.ResolveStatementSingleOthers
import Belay.Sqlite.Model.StatementSingleton

set_option doc.verso true

/-! Which statements can have more than one possible execution (ADR 0019, D4, amended 2026-10-25). Only
the resolver of INSERT from a query gives a statement without rules that is an INSERT from a query
({name}`Belay.Sqlite.Model.Resolved.Statement.fromQuery`); every other resolver gives a statement of
another form. So a script whose statements are no INSERT from a query has one execution for each of them. -/

namespace Belay.Sqlite.Model

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
  | .createView .. | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropTable .. | .dropView ..
  | .dropIndex .. | .dropTrigger .. | .begin | .commit | .rollback | .insert .. | .update .. | .delete .. | .select ..
  | .pragma _ => false

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
  case renameTable =>
    exact plain _ ok fun _ _ found => by
      rcases resolveRenameTable_outcome _ _ _ _ _ _ found with ⟨_, _, rfl⟩ | ⟨rfl, _⟩ <;> rfl
  case renameColumn =>
    exact plain _ ok fun _ _ found => by
      rcases resolveRenameColumn_outcome _ _ _ _ _ _ _ _ _ found with ⟨_, _, rfl⟩ | ⟨rfl, _⟩ <;> rfl
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
