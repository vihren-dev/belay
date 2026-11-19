import Belay.Sqlite.Model.Schema.Columns.ResolveAddColumnCatalog
import Belay.Sqlite.Model.Schema.Ddl.NamesSpec

set_option doc.verso true

/-! Facts that the resolver supplies about the input catalog and the resulting statement. -/

namespace Belay.Sqlite.Model

/-- The facts about the input catalog for each resolved statement.
* CREATE TABLE, VIEW, TRIGGER and INDEX append at the end. An index also refers to a table.
* ADD COLUMN refers to a table and the default fits its strict type ({name}`strictDefaultFits`).
* DROP COLUMN removes a droppable column and stores the catalog with that column removed.
* A rewrite preserves the catalog outline ({name}`Catalog.sameOutline`).
* DROP removes positions closed under dependencies ({name}`Catalog.DropClosed`).
* Other statements require nothing.

For example, {lean}`(Resolved.Statement.begin).SchemaLink []` holds. -/
def Resolved.Statement.SchemaLink (catalog : Catalog) : Resolved.Statement → Prop
  | .createTable target .. | .createView target .. | .createTrigger target .. => target = catalog.length
  | .createIndex target _ index => target = catalog.length ∧ (catalog.tableAt index.table).isSome = true
  | .addColumn target column _ => (catalog.tableAt target).isSome = true ∧ strictDefaultFits column = true
  | .dropColumn target index stored => catalog.droppable target index = true ∧ stored = catalog.dropColumn target index
  | .drop positions _ => catalog.DropClosed positions
  | .rewrite renamed => catalog.sameOutline renamed = true
  | .begin | .commit | .rollback | .insert ..
  | .update .. | .upsert .. | .insertSelect .. | .delete .. | .prepareError _ | .query .. | .setting _ _ => True

/-- For every successful resolution of CREATE TABLE, the resolved statement meets
{name}`Resolved.Statement.SchemaLink` on the catalog. Proof sketch: every branch of the resolver gives a
prepare error or a CREATE TABLE. -/
theorem resolveCreateTable_schemaLink (context : ResolveContext) (catalog after : Catalog)
    (name : Identifier) (columns : List Syntax.ColumnDefinition) (constraints : List Syntax.TableConstraint)
    (options : Syntax.TableOptions) (statement : Resolved.Statement)
    (ok : resolveCreateTable context catalog name columns constraints options = .ok (statement, after)) :
    statement.SchemaLink catalog := by
  unfold resolveCreateTable at ok
  simp only [issueResolution, prepareError, restrict] at ok
  repeat' split at ok
  all_goals first | (cases ok; trivial) | (cases ok; exact Catalog.DropClosed.nil _) | (cases ok)

/-- For every successful resolution of CREATE INDEX, the resolved statement meets
{name}`Resolved.Statement.SchemaLink` on the catalog. Proof sketch: every branch of the resolver gives a
prepare error or a CREATE INDEX. -/
theorem resolveCreateIndex_schemaLink (context : ResolveContext) (catalog after : Catalog)
    (name : Identifier) (unique : Bool) (tableName : Identifier) (terms : List Syntax.OrderTerm)
    (filter : Option Syntax.Expr) (statement : Resolved.Statement)
    (ok : resolveCreateIndex context catalog name unique tableName terms filter = .ok (statement, after)) :
    statement.SchemaLink catalog := by
  unfold resolveCreateIndex at ok
  simp only [issueResolution, prepareError, restrict] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; trivial)
    | (cases ok; exact ⟨rfl, by rw [Catalog.tableAt_of_findTable (by assumption)]; rfl⟩)
    | cases ok

/-- For every successful resolution of CREATE TRIGGER, the resolved statement meets
{name}`Resolved.Statement.SchemaLink` on the catalog. Proof sketch: every branch of the resolver gives a
prepare error, a CREATE TRIGGER, or (CREATE TRIGGER IF NOT EXISTS of an existing trigger) a DROP of no object,
which meets the link by {name}`Catalog.DropClosed.nil`. -/
theorem resolveCreateTrigger_schemaLink (catalog after : Catalog) (name : Identifier)
    (ifNotExists : Bool) (trigger : CatalogTrigger) (statement : Resolved.Statement)
    (ok : resolveCreateTrigger catalog name ifNotExists trigger = .ok (statement, after)) :
    statement.SchemaLink catalog := by
  unfold resolveCreateTrigger at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first | (cases ok; trivial) | (cases ok; exact Catalog.DropClosed.nil _) | (cases ok)

/-- For every successful resolution of INSERT, the resolved statement meets
{name}`Resolved.Statement.SchemaLink` on the catalog. Proof sketch: every branch of the resolver gives a write
or a prepare error. -/
theorem resolveInsert_schemaLink (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (names : Option (List Identifier)) (rows : List (List Syntax.Expr))
    (conflicts : List Syntax.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query) (shapes : SubqueryShapes)
    (statement : Resolved.Statement)
    (ok : resolveInsert context catalog tableName names rows conflicts algorithm returning subqueries shapes =
      .ok (statement, after)) : statement.SchemaLink catalog := by
  unfold resolveInsert resolveInsertTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first | (cases ok; trivial) | (cases ok; exact Catalog.DropClosed.nil _) | (cases ok)

/-- For every successful resolution of UPDATE, the resolved statement meets
{name}`Resolved.Statement.SchemaLink` on the catalog. Proof sketch: every branch of the resolver gives a write
or a prepare error. -/
theorem resolveUpdate_schemaLink (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (assignments : List (Identifier × Syntax.Expr)) (filter : Option Syntax.Expr)
    (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query) (shapes : SubqueryShapes)
    (statement : Resolved.Statement)
    (ok : resolveUpdate context catalog tableName assignments filter returning subqueries shapes =
      .ok (statement, after)) : statement.SchemaLink catalog := by
  unfold resolveUpdate resolveUpdateTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first | (cases ok; trivial) | (cases ok; exact Catalog.DropClosed.nil _) | (cases ok)

/-- For every successful resolution of DELETE, the resolved statement meets
{name}`Resolved.Statement.SchemaLink` on the catalog. Proof sketch: every branch of the resolver gives a write
or a prepare error. -/
theorem resolveDelete_schemaLink (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (filter : Option Syntax.Expr) (returning : List Syntax.ResultColumn)
    (subqueries : List Resolved.Query) (shapes : SubqueryShapes) (statement : Resolved.Statement)
    (ok : resolveDelete context catalog tableName filter returning subqueries shapes = .ok (statement, after)) :
    statement.SchemaLink catalog := by
  unfold resolveDelete resolveDeleteTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first | (cases ok; trivial) | (cases ok; exact Catalog.DropClosed.nil _) | (cases ok)

/-- For every successful resolution of a {lit}`SELECT`, the resolved statement meets
{name}`Resolved.Statement.SchemaLink` on the catalog. Proof sketch: every branch of the resolver gives a query
or a prepare error. -/
theorem resolveSelect_schemaLink (context : ResolveContext) (catalog after : Catalog)
    (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) (statement : Resolved.Statement)
    (ok : resolveSelect context catalog query subqueries = .ok (statement, after)) :
    statement.SchemaLink catalog := by
  unfold resolveSelect resolveSelectTraced at ok
  dsimp only [Traced.drop] at ok
  simp only [prepareError, issueResolution] at ok
  repeat' split at ok
  all_goals first | (cases ok; trivial) | (cases ok; exact Catalog.DropClosed.nil _) | (cases ok)

/-- For every pragma, state and successful resolution of the pragma, the resolved statement meets
{name}`Resolved.Statement.SchemaLink` on the catalog of the state. Proof sketch: by cases on the pragma; each branch
is a setting, a query or a prepare error. -/
theorem resolvePragma_schemaLink {state next : ResolveState} {pragma : Syntax.Pragma}
    {resolved : Resolved.Statement} (ok : resolvePragma state pragma = .ok (resolved, next)) :
    resolved.SchemaLink state.catalog := by
  unfold resolvePragma at ok
  repeat' split at ok
  all_goals first | (cases ok; trivial) | (cases ok; exact Catalog.DropClosed.nil _) | (cases ok)

/-- For every write resolution that meets {name}`Resolved.Statement.SchemaLink` on the catalog
({lit}`each`), every successful resolution of its subqueries and then of the write
({name}`resolveWriteSubqueries`) meets it. Proof
sketch: the other branches are a prepare error or a restriction. -/
theorem resolveWriteSubqueries_schemaLink {columnNames : List (Nat × List Identifier)} (context : ResolveContext) (catalog after : Catalog)
    (field : Nat) (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : List Resolved.Query → SubqueryShapes → StatementResolution) (statement : Resolved.Statement)
    (each : ∀ resolved shapes after statement, resolveWrite resolved shapes = .ok (statement, after) →
      statement.SchemaLink catalog)
    (ok : resolveWriteSubqueries context catalog field tableName scopeOf subqueries resolveWrite columnNames =
      .ok (statement, after)) : statement.SchemaLink catalog := by
  unfold resolveWriteSubqueries resolveWriteSubqueriesTraced resolveViewTargetTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; trivial)
    | (cases ok; exact Catalog.DropClosed.nil _)
    | (cases ok)
    | (obtain h | ⟨rfl, error, rfl⟩ := resolveViewTarget_cases ok; exact each _ _ _ _ h; trivial)
    | exact each _ _ _ _ ok

/-- For every write resolution that meets the schema-link predicate for every copied
query mapping, successful WITH expansion and write resolution also meet that predicate.
Proof sketch: the wrapper's other successful branches are prepare errors; the write branch
has the assumed schema link regardless of its copied queries and explicit column names. -/
theorem resolveCommonTableWrite_schemaLink (context : ResolveContext) (catalog after : Catalog)
    (field : Nat) (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : (Nat → Nat) → List Resolved.Query → SubqueryShapes → StatementResolution)
    (statement : Resolved.Statement)
    (each : ∀ index resolved shapes after statement, resolveWrite index resolved shapes = .ok (statement, after) →
      statement.SchemaLink catalog)
    (ok : resolveCommonTableWrite context catalog field tableName scopeOf subqueries resolveWrite =
      .ok (statement, after)) : statement.SchemaLink catalog := by
  unfold resolveCommonTableWrite resolveCommonTableWriteTraced resolveViewTargetTraced at ok
  simp only [resolveWriteSubqueriesTraced, traced_drop, prepareError, restrict, issueResolution, Except.mapError] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; trivial)
    | (cases ok; exact Catalog.DropClosed.nil _)
    | (cases ok)
    | (obtain h | ⟨rfl, error, rfl⟩ := resolveViewTarget_cases ok; exact each _ _ _ _ _ h; trivial)
    | exact each _ _ _ _ _ ok
  all_goals
    rename_i found
    repeat' split at found
    all_goals first
      | (cases found; trivial)
      | (cases found; exact Catalog.DropClosed.nil _)
      | (cases found)
      | (obtain h | ⟨rfl, error, rfl⟩ := resolveViewTarget_cases found; exact each _ _ _ _ _ h; trivial)
      | exact each _ _ _ _ _ found

end Belay.Sqlite.Model
