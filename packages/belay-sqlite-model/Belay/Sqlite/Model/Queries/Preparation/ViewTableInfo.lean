import Belay.Sqlite.Model.Queries.Preparation.ViewColumns
import Belay.Sqlite.Model.Queries.Preparation.PragmaResolution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The row of {lit}`PRAGMA table_info` for column {lit}`cid` of a view: its name, its normalized
declared type or the empty text, then {lit}`notnull` 0, {lit}`dflt_value` NULL and {lit}`pk` 0. -/
def viewInfoRow (cid : Nat) (column : CatalogColumn) : List Value :=
  [.integer cid, .text column.name.bytes, pragmaText (column.declaredType.getD ""),
    .integer 0, .null, .integer 0]

/-- The pragma query of the columns of a view. -/
def viewInfoStatement (columns : List CatalogColumn) : Resolved.Statement :=
  .query (pragmaQuery (.fixed tableInfoNames.length
    (columns.zipIdx.map fun (column, cid) => viewInfoRow cid column)) tableInfoNames) []

/-- Resolve {lit}`PRAGMA table_info(view)` for a name that the catalog holds as a view: the
rows of {name}`viewInfoRow` for the columns that {name}`viewColumns` reads, as the resolver of
a SELECT expands the view now. SQLite reads the columns only to describe them, so a query
error that it finds only when a statement runs the view, and the width check of the view's own
explicit name list, are not errors of the pragma ({name}`viewPrepareFailure`). A missing table
or a cycle is the prepare error of the pragma. The state is unchanged. -/
def resolveViewTableInfo (context : ResolveContext) (state : ResolveState) (view : Identifier) :
    Except NodeRestriction (Resolved.Statement × ResolveState) :=
  match viewColumns context state.catalog view with
  | .ok columns => .ok (viewInfoStatement columns, state)
  | .error issue => (readIssueResolution state.catalog issue).map fun (statement, _) => (statement, state)

end Belay.Sqlite.Model
