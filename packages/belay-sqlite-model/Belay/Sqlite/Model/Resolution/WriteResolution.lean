import Belay.Sqlite.Model.Resolution.Updates
import Belay.Sqlite.Model.Resolution.Deletes
import Belay.Sqlite.Model.Resolution.SubqueryResolution

set_option doc.verso true

/-! Resolution of the subqueries of a write (ADR 0018, D1): {lit}`INSERT`, {lit}`UPDATE` and
{lit}`DELETE` resolve their subqueries ({lit}`SubqueryResolution`) around the scope of the
written table, or around no table for the {lit}`VALUES` of {lit}`INSERT`, and then their own
expressions with the subqueries' shapes. A subquery that reads the written table is a
restriction: SQLite evaluates an uncorrelated subquery once, but a correlated one over the rows
that the statement has already changed (checked natively: {lit}`UPDATE t SET a = (SELECT
count(*) FROM t AS b WHERE b.a < t.a) + 10` over 1, 2, 3 gives 10, 10, 10). -/

namespace Belay.Sqlite.Model

/-- Resolve the subqueries of a write to the table {lit}`tableName`, whose syntax holds them at
child {lit}`field`, around the scope that {lit}`scopeOf` gives for the table, then the write
with them ({lit}`resolveWrite`). The optional {lit}`columnNames` supplies explicit CTE
output names; use the empty default for ordinary subqueries. A subquery that reads the written table directly is
{name}`RestrictionKind.subqueryReadsTarget`. An unexpanded view target is restricted
before the write's subqueries can produce an error with the wrong precedence. -/
def resolveWriteSubqueries (context : ResolveContext) (catalog : Catalog) (field : Nat) (tableName : Identifier)
    (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : List Resolved.Query → SubqueryShapes → StatementResolution)
    (columnNames : List (Nat × List Identifier) := []) : StatementResolution :=
  if (catalog.findView tableName).isSome then restrict [0] .subqueryHere else
  let target := catalog.findTable tableName
  let scope := (target.map fun (_, table) => scopeOf table).getD []
  match resolveSubqueries context.profile.dqsDml catalog field (QueryScope.ofScope scope) subqueries columnNames with
  | .error (.noSuchTable name) => prepareError catalog (.noSuchTable name)
  | .error (.value issue) => issueResolution catalog [] issue
  | .ok (resolved, shapes) =>
    if target.any fun (position, _) => resolved.any (·.readsTable position) then
      restrict [field] .subqueryReadsTarget
    else resolveWrite resolved { later := shapes }

/-- The scope of the written table of {lit}`UPDATE` and {lit}`DELETE`, as their expressions see it. -/
def writtenScope (tableName : Identifier) (table : CatalogTable) : Scope :=
  Scope.single tableName table.columns !table.withoutRowid

end Belay.Sqlite.Model
