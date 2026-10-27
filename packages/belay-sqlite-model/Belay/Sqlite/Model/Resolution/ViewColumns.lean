import Belay.Sqlite.Model.Resolution.SelectResolution
import Belay.Sqlite.Model.Resolution.ViewReadErrors

set_option doc.verso true

/-! The columns of a view, as SQLite reads them when a statement needs them (ADR 0017): the
resolver of {lit}`SELECT * FROM view` gives them, and the errors of the view's query that
SQLite finds at that point ({lit}`ExprError.viewReadClass`) are the errors of the
statement. A statement that reads the view's columns is {lit}`PRAGMA table_info` of the view
and a write to it. -/

namespace Belay.Sqlite.Model

/-- The query {lit}`SELECT * FROM view` that supplies the columns of a view. -/
def viewColumnsQuery (view : Identifier) : Syntax.Subquery :=
  { columns := [.star], source := some { table := view, alias := none }, joins := [], filter := none,
    groupBy := [], orderBy := [], limit := none, offset := none, parent := none }

/-- The columns of a view whose explicit name list has another width than its query. SQLite
keeps the names of the list, with its duplicate-name suffixes, and no declared types, because it
copies the types only when the widths agree. The columns are those of the name list over a body of
literals with the same width, resolved by the ordinary select resolver; none when that fails. -/
def widthMismatchColumns (context : ResolveContext) (view : Identifier) (names : List Identifier) :
    Option (List CatalogColumn) :=
  let literals : Syntax.Subquery :=
    { columns := names.map fun _ => .expression .null none "NULL", source := none, joins := [],
      filter := none, groupBy := [], orderBy := [], limit := none, offset := none, parent := none }
  match resolveSelectDetails context (Catalog.createView [] view { columns := some names, query := literals })
      (viewColumnsQuery view) [] with
  | .ok (_, _, [source]) => some source.columns
  | .ok (_, _, []) | .ok (_, _, _ :: _ :: _) | .error _ => none

/-- The issue for a view body that the model cannot place before the statement runs. -/
def viewBodyCheck : SourceIssue := .value (.restriction [] .viewBodyCheck)

/-- The result of reading the columns of a view when the view's query fails with a prepare
error ({name}`ExprError.viewReadClass`). The width check of the view's own explicit name list
is not part of the read: the columns are those of {name}`widthMismatchColumns`. The same
check of another view, which SQLite also skips, is the restriction
{name}`RestrictionKind.viewBodyCheck`, because the model has no columns for it. So is an error that
SQLite finds only when a statement runs the view. Any other error stays the error. -/
def viewPrepareFailure (context : ResolveContext) (catalog : Catalog) (view : Identifier) (error : ExprError) :
    Except SourceIssue (List CatalogColumn) :=
  match error.viewReadClass with
  | .found | .column => .error (.value (.prepare error))
  | .later => .error viewBodyCheck
  | .width name =>
    match (catalog.findView view).bind (·.2.columns) with
    | some names =>
      if name.sameName view then
        match widthMismatchColumns context view names with
        | some columns => .ok columns
        | none => .error viewBodyCheck
      else .error viewBodyCheck
    | none => .error viewBodyCheck

/-- The columns of a view as SQLite reads them: the columns of {lit}`SELECT * FROM view`
({name}`viewColumnsQuery`) resolved by the select resolver, or the issue that the read fails
with. A missing table is its issue. A model restriction of the query stays that restriction. -/
def viewColumns (context : ResolveContext) (catalog : Catalog) (view : Identifier) :
    Except SourceIssue (List CatalogColumn) :=
  match resolveSelectDetails context catalog (viewColumnsQuery view) [] with
  | .ok (_, _, [source]) => .ok source.columns
  | .ok (_, _, []) | .ok (_, _, _ :: _ :: _) => .error viewBodyCheck
  | .error (.noSuchTable name) => .error (.noSuchTable name)
  | .error (.value (.restriction path kind)) => .error (.value (.restriction path kind))
  | .error (.value (.prepare error)) => viewPrepareFailure context catalog view error

/-- The statement resolution of an issue of reading a view: a missing table or a prepare error
keeps the catalog, and a restriction refuses the script. -/
def readIssueResolution (catalog : Catalog) : SourceIssue → StatementResolution
  | .noSuchTable name => prepareError catalog (.noSuchTable name)
  | .value issue => issueResolution catalog [] issue

/-- The name of the view in a write that SQLite refuses with {name}`PrepareError.viewModify`, and
none for every other prepare error. -/
def PrepareError.viewModified? : PrepareError → Option Identifier
  | .viewModify name => some name
  | .viewVariables | .tableExists _ | .viewExists _ | .indexNameUsed _ | .tableNameUsed _
  | .indexExists _ | .noSuchTable _ | .noSuchView _ | .useDropTable _ | .useDropView _
  | .noSuchIndex _ | .tableMayNotBeDropped _ | .noSuchReferencedTable _ | .foreignKeyMismatch ..
  | .noSuchTrigger _ | .triggerExists _ | .viewNotIndexed | .viewAddColumn | .viewTrigger .. | .renameTargetTaken _
  | .viewNotAltered _ | .viewColumnsNotRenamed _ | .renameNoSuchColumn _ | .dependentObject ..
  | .expression _ => none

/-- Whether a resolved statement is the refusal of a write to a view
({name}`PrepareError.viewModified?`). -/
def Resolved.Statement.isViewModify : Resolved.Statement → Bool
  | .prepareError error => error.viewModified?.isSome
  | .createView .. | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .rewrite _ | .dropColumn ..
  | .drop .. | .begin | .commit | .rollback | .setting .. | .query .. | .insert .. | .update ..
  | .upsert .. | .insertSelect .. | .delete .. => false

/-- Complete the resolution of a write to a view ({name}`resolveViewModify`): SQLite reads the
columns of the view first, so a view that it cannot read gives that error instead; any other
error of the write, such as the rows of an INSERT with different widths, which the parser finds
first, stays. -/
def resolveViewTarget (context : ResolveContext) (catalog : Catalog) (view : Identifier)
    (written : StatementResolution) : StatementResolution :=
  match written with
  | .error restriction => .error restriction
  | .ok (statement, after) =>
    if statement.isViewModify then
      match viewColumns context catalog view with
      | .ok _ => .ok (statement, after)
      | .error issue => readIssueResolution catalog issue
    else .ok (statement, after)

/-- For every completed write to a view that resolves, either the write itself resolved to that
result, or the result is a prepare error that leaves the catalog as it was (the read of the
view failed). Proof sketch: the completion changes only the one branch of a view-modify error,
and there it gives the same result or the prepare error of a failed read. -/
theorem resolveViewTarget_cases {context : ResolveContext} {catalog after : Catalog} {view : Identifier}
    {written : StatementResolution} {statement : Resolved.Statement}
    (ok : resolveViewTarget context catalog view written = .ok (statement, after)) :
    written = .ok (statement, after) ∨ (after = catalog ∧ ∃ error, statement = .prepareError error) := by
  unfold resolveViewTarget at ok
  split at ok
  · cases ok
  · rename_i written' after'
    split at ok
    · cases read : viewColumns context catalog view with
      | ok columns =>
        rw [read] at ok
        cases ok
        left
        rfl
      | error issue =>
        rw [read] at ok
        right
        cases issue with
        | noSuchTable name =>
          simp only [readIssueResolution, prepareError] at ok
          cases ok
          exact ⟨rfl, _, rfl⟩
        | value inner =>
          cases inner <;> simp only [readIssueResolution, issueResolution, prepareError, restrict] at ok
          · cases ok
            exact ⟨rfl, _, rfl⟩
          · cases ok
    · cases ok
      left
      rfl

end Belay.Sqlite.Model
