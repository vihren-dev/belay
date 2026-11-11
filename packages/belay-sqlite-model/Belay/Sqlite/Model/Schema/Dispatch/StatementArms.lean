import Belay.Sqlite.Model.Schema.Dispatch.ResolveStatement
import Belay.Sqlite.Model.Frontend.Codecs.StatementAttr
import Belay.Sqlite.Model.Queries.Preparation.WriteTracedLaws

set_option doc.verso true

/-! The equations of {lit}`resolveStatement` for each form of a statement, in the shape that the
function had before the name trace. The function is the projection of
{lit}`resolveStatementTraced`; these equations restate its old body, so that proofs about
the resolution of a statement find the steps that they use. -/

namespace Belay.Sqlite.Model

/-- For every context, state and statement: the first component of {name}`resolveStatementTraced` is
{name}`resolveStatement`. Plain words: the trace entry point decides the statement as the untraced
function does, for success and for failure. Proof sketch: {name}`resolveStatement` is defined as that
component. -/
theorem resolveStatementTraced_fst (context : ResolveContext) (state : ResolveState)
    (statement : Syntax.Statement) :
    (resolveStatementTraced context state statement).1 = resolveStatement context state statement := rfl

/-- BEGIN always succeeds. It keeps the saved catalog when there is one, else it saves the current
catalog. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_begin (context : ResolveContext) (state : ResolveState) :
    resolveStatement context state .begin = .ok (.begin, { state with saved := state.saved.getD state.catalog }) := rfl

/-- COMMIT always succeeds and drops the saved catalog, whether there is one or not. Proof sketch: both
sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_commit (context : ResolveContext) (state : ResolveState) :
    resolveStatement context state .commit = .ok (.commit, { state with saved := none }) := rfl

/-- ROLLBACK always succeeds. It restores the saved catalog when there is one, keeps the current catalog
otherwise, and drops the saved catalog in both cases. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_rollback (context : ResolveContext) (state : ResolveState) :
    resolveStatement context state .rollback =
      .ok (.rollback, { state with catalog := state.saved.getD state.catalog, saved := none }) := rfl

/-- A pragma resolves with {name}`resolveStatementPragma`. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_pragma (context : ResolveContext) (state : ResolveState)
    (pragma : Syntax.Pragma) :
    resolveStatement context state (.pragma pragma) = resolveStatementPragma context state pragma := rfl

/-- CREATE VIEW resolves against the catalog of the state. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_createView (context : ResolveContext) (state : ResolveState)
    (name : Identifier) (ifNotExists : Bool) (columns : Option (List Identifier)) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) :
    resolveStatement context state (.createView name ifNotExists columns query subqueries) =
      state.withCatalog (resolveCreateView state.catalog name ifNotExists { columns, query, subqueries }) := rfl

/-- ALTER TABLE ADD COLUMN resolves against the catalog and the foreign key setting of the state. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_addColumn (context : ResolveContext) (state : ResolveState)
    (table : Identifier) (column : Syntax.ColumnDefinition) :
    resolveStatement context state (.addColumn table column) =
      state.withCatalog (resolveAddColumn context state.catalog state.foreignKeys table column) := rfl

/-- CREATE TRIGGER resolves against the catalog of the state. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_createTrigger (context : ResolveContext) (state : ResolveState)
    (name : Identifier) (ifNotExists : Bool) (time : Syntax.TriggerTime) (event : Syntax.TriggerEvent)
    (table : Identifier) (condition : Option Syntax.Expr) (body : List Syntax.BodyStatement) :
    resolveStatement context state (.createTrigger name ifNotExists time event table condition body) =
      state.withCatalog (resolveCreateTrigger state.catalog name ifNotExists
        { table, time, event, condition, body }) := rfl

/-- DROP TRIGGER resolves against the catalog of the state. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_dropTrigger (context : ResolveContext) (state : ResolveState)
    (name : Identifier) (ifExists : Bool) :
    resolveStatement context state (.dropTrigger name ifExists) =
      state.withCatalog (resolveDropTrigger state.catalog name ifExists) := rfl

/-- INSERT is a write: its CTEs and views are copied first, then the rows, conflicts and
{lit}`RETURNING` resolve. Proof sketch: unfold the entry point and the projection of the traced write with {lit}`traced_drop`; then both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_insert (context : ResolveContext) (state : ResolveState)
    (table : Identifier) (columns : Option (List Identifier)) (rows : List (List Syntax.Expr))
    (conflicts : List Syntax.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (returning : List Syntax.ResultColumn) (subqueries : List Syntax.Subquery) :
    resolveStatement context state (.insert table columns rows conflicts algorithm returning subqueries) =
      state.withWrite context (resolveCommonTableWrite context state.catalog 6 table (fun _ => []) subqueries
        (fun index => resolveInsert context state.catalog table columns
          (rows.map (List.map (Syntax.Expr.reindex index))) conflicts algorithm returning)) := by
  simp only [resolveStatement, resolveStatementTraced, resolveStatementRun, ResolveState.withWriteTraced,
    traced_drop]
  rfl

/-- INSERT from a query is a write whose resolution is {name}`resolveInsertQueryTraced`. Proof sketch:
unfold the entry point and the projection of the traced write with {lit}`traced_drop`; then both sides are
equal by definition. -/
@[statement_arms] theorem resolveStatement_insertSelect (context : ResolveContext) (state : ResolveState)
    (table : Identifier) (columns : Option (List Identifier)) (body : Syntax.SelectBody)
    (conflicts : List Syntax.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (returning : List Syntax.ResultColumn) :
    resolveStatement context state (.insertSelect table columns body conflicts algorithm returning) =
      state.withWrite context
        (resolveInsertQueryTraced context state.catalog table columns body conflicts algorithm returning).drop := by
  simp only [resolveStatement, resolveStatementTraced, resolveStatementRun, ResolveState.withWriteTraced,
    traced_drop]

/-- UPDATE is a write: its CTEs and views are copied first, then the assignments, filter and
{lit}`RETURNING` resolve. Proof sketch: unfold the entry point and the projection of the traced write with {lit}`traced_drop`; then both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_update (context : ResolveContext) (state : ResolveState)
    (table : Identifier) (assignments : List (Identifier × Syntax.Expr)) (filter : Option Syntax.Expr)
    (returning : List Syntax.ResultColumn) (subqueries : List Syntax.Subquery) :
    resolveStatement context state (.update table assignments filter returning subqueries) =
      state.withWrite context (resolveCommonTableWrite context state.catalog 4 table (writtenScope table) subqueries
        (fun index => resolveUpdate context state.catalog table
          (assignments.map fun (name, value) => (name, value.reindex index))
          (filter.map (Syntax.Expr.reindex index)) returning)) := by
  simp only [resolveStatement, resolveStatementTraced, resolveStatementRun, ResolveState.withWriteTraced,
    traced_drop]
  rfl

/-- DELETE is a write: its CTEs and views are copied first, then the filter and {lit}`RETURNING`
resolve. Proof sketch: unfold the entry point and the projection of the traced write with {lit}`traced_drop`; then both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_delete (context : ResolveContext) (state : ResolveState)
    (table : Identifier) (filter : Option Syntax.Expr) (returning : List Syntax.ResultColumn)
    (subqueries : List Syntax.Subquery) :
    resolveStatement context state (.delete table filter returning subqueries) =
      state.withWrite context (resolveCommonTableWrite context state.catalog 3 table (writtenScope table) subqueries
        (fun index => resolveDelete context state.catalog table (filter.map (Syntax.Expr.reindex index))
          returning)) := by
  simp only [resolveStatement, resolveStatementTraced, resolveStatementRun, ResolveState.withWriteTraced,
    traced_drop]
  rfl

/-- SELECT resolves against the catalog of the state. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_select (context : ResolveContext) (state : ResolveState)
    (columns : List Syntax.ResultColumn) (source : Option Syntax.TableReference) (joins : List Syntax.Join)
    (filter : Option Syntax.Expr) (groupBy : List Syntax.Expr) (orderBy : List Syntax.OrderTerm)
    (limit offset : Option Syntax.Expr) (subqueries : List Syntax.Subquery) (having : Option Syntax.Expr)
    (distinct : Bool) (compound : Option Syntax.Compound) :
    resolveStatement context state (.select columns source joins filter groupBy orderBy limit offset subqueries
      having distinct compound) =
      state.withCatalog (resolveSelect context state.catalog
        { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct,
          compound } subqueries) := rfl

end Belay.Sqlite.Model
