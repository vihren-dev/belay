import Belay.Sqlite.Resolution.Writes

set_option doc.verso true

/-! Resolution of UPDATE (ADR 0012, amendment 1, "Resolved forms"): each {lit}`SET`
value is an expression over the table's columns, and the {lit}`WHERE` filter is a
condition, both resolved as in {lit}`SELECT`. A value that names no column folds to
the literal of its stored value. A value that reads the row may not assign a column of
a unique key: that is a model restriction. -/

namespace Belay.Sqlite

/-- The resolved value of one {lit}`SET` assignment for the column at
{lit}`position`: the literal of its stored value ({name}`storeValue`) when the
expression names no column, otherwise the expression, which the execution evaluates on
the old row and stores. -/
def assignedExpression (columns : List CatalogColumn) (position : Nat) (expression : Syntax.Expr)
    (resolved : Resolved.Expr) : Resolved.Expr :=
  if mentionsColumn columns expression then resolved
  else .literal (storeValue (columnAffinity columns position) (resolved.eval []))

/-- Resolve one {lit}`SET` assignment at item {lit}`item`, in SQLite's order
({lit}`sqlite3Update`): the expression first, then the column name. The column name
must name a column of the table ({lit}`no such column: %s`). A value that reads the
row for a column of a unique key ({lit}`keyColumns`) is a model restriction. Paths are
relative to the assignment list. -/
def resolveAssignment (dqs : Bool) (columns : List CatalogColumn) (keyColumns : List Nat) (item : Nat) :
    String × Syntax.Expr → Except ValueIssue (Nat × Resolved.Expr)
  | (name, value) =>
    (resolveOperand dqs columns true value).mapError (·.under [item, 1]) >>= fun operand =>
    (match columnPosition columns name with
      | some position => .ok position
      | none => .error (.prepare (.noSuchColumn name))) >>= fun position =>
    if mentionsColumn columns value && keyColumns.contains position then
      .error (.restriction [item, 1] .rowDependentKey)
    else .ok (position, assignedExpression columns position value operand.1)

/-- The written key values of a resolved UPDATE: the literal assignments, as positions
and values, for the key-domain check ({name}`keyDomainRestriction`). An assignment to a
key column is always a literal, because {name}`resolveAssignment` refuses others. -/
def literalAssignments (assignments : List (Nat × Resolved.Expr)) : List (Nat × Value) :=
  assignments.filterMap fun
    | (position, .literal value) => some (position, value)
    | _ => none

/-- Resolve UPDATE. Path 1 is the assignment list, path 2 the filter and path 3 the
{lit}`RETURNING` columns, which resolve last. The assignments resolve in order, then
the filter as a condition; then a column assigned twice and the key domain are model
restrictions. -/
def resolveUpdate (context : ResolveContext) (catalog : Catalog) (index : Nat) (tableName : String)
    (assignments : List (String × Syntax.Expr)) (filter : Option Syntax.Expr)
    (returning : List Syntax.ResultColumn) : StatementResolution :=
  let dqs := context.profile.dqsDml
  match catalog.findTable tableName with
  | none => prepareError catalog (.noSuchTable tableName)
  | some (position, table) =>
    let keys := catalog.uniqueKeys position table
    match resolveAll (resolveAssignment dqs table.columns keys.flatten) assignments with
    | .error issue => issueResolution catalog index [1] issue
    | .ok resolved =>
      let resolvedCondition : Except ValueIssue (Option Resolved.Expr) := match filter with
        | none => .ok none
        | some term => some <$> condition [] (resolveOperand dqs table.columns true term)
      match resolvedCondition with
      | .error issue => issueResolution catalog index [2] issue
      | .ok resolvedFilter =>
        let positions := resolved.map Prod.fst
        if positions.eraseDups.length != positions.length then
          restrict index [1] .updateColumnTwice
        else match keyDomainRestriction table.columns keys (fun _ => [1]) [literalAssignments resolved] with
          | some (path, reason) => restrict index path reason
          | none => match resolveReturning dqs table.columns returning with
            | .error issue => issueResolution catalog index [3] issue
            | .ok columns => .ok (.update position resolved resolvedFilter keys columns, catalog)

end Belay.Sqlite
