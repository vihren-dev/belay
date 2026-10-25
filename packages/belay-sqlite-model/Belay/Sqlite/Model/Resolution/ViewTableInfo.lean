import Belay.Sqlite.Model.Resolution.SelectResolution
import Belay.Sqlite.Model.Resolution.PragmaResolution

set_option doc.verso true

/-! {lit}`PRAGMA table_info` of a view (ADR 0019, D5). SQLite reads the view's current columns
the way a query reads them, so the pragma reuses the select resolver: the rows describe the
columns of {lit}`SELECT * FROM view`. A view that SQLite cannot read gives the prepare error of
that query. -/

namespace Belay.Sqlite.Model

/-- The row of {lit}`PRAGMA table_info` for column {lit}`cid` of a view: its name, its normalized
declared type or the empty text, then {lit}`notnull` 0, {lit}`dflt_value` NULL and {lit}`pk` 0. -/
def viewInfoRow (cid : Nat) (column : CatalogColumn) : List Value :=
  [.integer cid, .text column.name.bytes, pragmaText (column.declaredType.getD ""),
    .integer 0, .null, .integer 0]

/-- The query {lit}`SELECT * FROM view` that supplies the columns of a view. -/
def viewColumnsQuery (view : Identifier) : Syntax.Subquery :=
  { columns := [.star], source := some { table := view, alias := none }, joins := [], filter := none,
    groupBy := [], orderBy := [], limit := none, offset := none, parent := none }

/-- The pragma query of the columns of a view. -/
def viewInfoStatement (columns : List CatalogColumn) : Resolved.Statement :=
  .query (pragmaQuery (.fixed tableInfoNames.length
    (columns.zipIdx.map fun (column, cid) => viewInfoRow cid column)) tableInfoNames) []

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
  | _ => none

/-- Resolve {lit}`PRAGMA table_info(view)` for a name that the catalog holds as a view: the
rows of {name}`viewInfoRow` for the columns of {name}`viewColumnsQuery`, as the resolver of a
SELECT expands the view now. A missing table, a cycle or another prepare error of the view's
query is the prepare error of the pragma; a model restriction of that query is a restriction
of the pragma. The one exception is the width check of the view's own explicit name list, which
only a use of the view in a query makes
({name}`widthMismatchColumns`). The state is unchanged. -/
def resolveViewTableInfo (context : ResolveContext) (state : ResolveState) (view : Identifier) :
    Except NodeRestriction (Resolved.Statement × ResolveState) :=
  match resolveSelectDetails context state.catalog (viewColumnsQuery view) [] with
  | .ok (_, _, [source]) => .ok (viewInfoStatement source.columns, state)
  | .ok _ => .error { path := [], kind := .subqueryHere }
  | .error (.noSuchTable name) => .ok (.prepareError (.noSuchTable name), state)
  | .error (.value issue) =>
    let other := (issueResolution state.catalog [] issue).map fun (statement, _) => (statement, state)
    match issue, (state.catalog.findView view).bind (·.2.columns) with
    | .prepare (.view (.columns name _ _)), some names =>
      if name.sameName view then
        match widthMismatchColumns context view names with
        | some columns => .ok (viewInfoStatement columns, state)
        | none => .error { path := [], kind := .subqueryHere }
      else other
    | _, _ => other

/-- Resolve a pragma statement: {lit}`PRAGMA table_info` of a view is {name}`resolveViewTableInfo`,
and every other pragma is {name}`resolvePragma`. -/
def resolveStatementPragma (context : ResolveContext) (state : ResolveState) :
    Syntax.Pragma → Except NodeRestriction (Resolved.Statement × ResolveState)
  | .tableInfo table =>
    if (state.catalog.findView table).isSome then resolveViewTableInfo context state table
    else resolvePragma state (.tableInfo table)
  | pragma => resolvePragma state pragma

/-- For every context, state and table choice, the statement resolution of
{lit}`PRAGMA foreign_key_check` is {name}`resolvePragma`: a view-aware table_info does not
change it. Proof sketch: the definition has a separate case for table_info only. -/
theorem resolveStatementPragma_foreignKeyCheck (context : ResolveContext) (state : ResolveState)
    (table : Option Identifier) :
    resolveStatementPragma context state (.foreignKeyCheck table) = resolvePragma state (.foreignKeyCheck table) :=
  rfl

/-- The statement-level form of {name}`resolvePragma_cases`: for every context, state and pragma
that resolves, either a setting with a value sets the state, or the next state is the state, the
catalog is unchanged and the statement is not control. Proof sketch: a view branch yields a query
or a prepare error with the state unchanged; the other pragmas are {name}`resolvePragma_cases`. -/
theorem resolveStatementPragma_cases {context : ResolveContext} {state next : ResolveState}
    {pragma : Syntax.Pragma} {resolved : Resolved.Statement}
    (ok : resolveStatementPragma context state pragma = .ok (resolved, next)) :
    (∃ setting on, resolved = .setting setting on ∧ next = state.set on setting) ∨
      (next = state ∧ resolved.applyCatalog state.catalog = state.catalog ∧ resolved.isControl = false) := by
  unfold resolveStatementPragma at ok
  split at ok
  · split at ok
    · unfold resolveViewTableInfo at ok
      simp only [issueResolution, prepareError, restrict, viewInfoStatement, Except.map] at ok
      repeat' split at ok
      all_goals first
        | (cases ok; exact .inr ⟨rfl, rfl, rfl⟩)
        | cases ok
        | skip
      all_goals
        rename_i heq
        first
          | (split at heq <;> first | (cases heq; exact .inr ⟨rfl, rfl, rfl⟩) | cases heq)
          | (cases heq; exact .inr ⟨rfl, rfl, rfl⟩)
    · exact resolvePragma_cases ok
  · exact resolvePragma_cases ok

end Belay.Sqlite.Model
