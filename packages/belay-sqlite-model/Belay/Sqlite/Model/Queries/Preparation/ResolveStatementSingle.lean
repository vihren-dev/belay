import Belay.Sqlite.Model.Queries.Preparation.ResolveStatementSingleOthers
import Belay.Sqlite.Model.Queries.Preparation.CommonTableWrites

set_option doc.verso true

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

/-- Whether the statement is INSERT from a query ({lit}`INSERT INTO t SELECT ...`), the one syntax whose
resolved statement can be an INSERT from a query without rules. -/
def Syntax.Statement.isInsertSelect : Syntax.Statement → Bool
  | .insertSelect .. => true
  | .createView .. | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn .. | .dropTable .. | .dropView ..
  | .dropIndex .. | .dropTrigger .. | .begin | .commit | .rollback | .insert .. | .update .. | .delete .. | .select ..
  | .pragma _ => false

end Belay.Sqlite.Model
