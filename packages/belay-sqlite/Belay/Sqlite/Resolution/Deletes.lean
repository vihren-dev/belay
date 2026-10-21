import Belay.Sqlite.Resolution.Writes

set_option doc.verso true

/-! Resolution of DELETE (ADR 0012, amendment 1, slice 3c): the {lit}`WHERE` filter is a
condition, resolved as in {lit}`SELECT`, and the {lit}`RETURNING` columns are resolved
over the table's columns. -/

namespace Belay.Sqlite

/-- Resolve DELETE. Path 1 is the filter and path {name}`deleteReturningField` the
{lit}`RETURNING` columns. SQLite's own tables are a model restriction, as in
{lit}`SELECT`. The filter may name the statement's resolved subqueries, whose shapes are
{lit}`shapes`. In a trigger's body, the filter also sees the trigger's rows {lit}`trigger`,
after the table's cells (ADR 0018, D5). -/
def resolveDelete (context : ResolveContext) (catalog : Catalog) (index : Nat) (tableName : Identifier)
    (filter : Option Syntax.Expr) (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query)
    (shapes : SubqueryShapes) (trigger : Option TriggerRow := none) : StatementResolution :=
  let dqs := context.profile.dqsDml
  match catalog.findTable tableName with
  | none =>
    if reservedName tableName then restrict index [0] .systemTable
    else prepareError catalog (.noSuchTable tableName)
  | some (position, table) =>
    let scope := Scope.single tableName table.columns !table.withoutRowid
    let resolvedCondition : Except ValueIssue (Option Resolved.Expr) := match filter with
      | none => .ok none
      | some term => some <$> condition [] (resolveOperand dqs (scope ++ (trigger.map (·.scope table.columns.length)).getD [])
          shapes true term)
    match resolvedCondition with
    | .error issue => issueResolution catalog index [1] issue
    | .ok resolvedFilter => match resolveReturning dqs scope returning with
      | .error issue => issueResolution catalog index [deleteReturningField] issue
      | .ok columns => .ok (.delete position resolvedFilter columns subqueries, catalog)

end Belay.Sqlite
