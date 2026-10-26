import Belay.Sqlite.Model.Resolution.Updates
import Belay.Sqlite.Model.Resolution.Deletes
import Belay.Sqlite.Model.Resolution.SubqueryResolution
import Belay.Sqlite.Model.Resolution.ViewColumns
import Belay.Sqlite.Model.Resolution.SourceStage

set_option doc.verso true

/-! Resolution of the subqueries of a write (ADR 0018, D1): {lit}`INSERT`, {lit}`UPDATE` and
{lit}`DELETE` resolve their subqueries ({lit}`SubqueryResolution`) around the scope of the
written table, or around no table for the {lit}`VALUES` of {lit}`INSERT`, and then their own
expressions with the subqueries' shapes. A subquery that reads the written table is a
restriction: SQLite evaluates an uncorrelated subquery once, but a correlated one over the rows
that the statement has already changed (checked natively: {lit}`UPDATE t SET a = (SELECT
count(*) FROM t AS b WHERE b.a < t.a) + 10` over 1, 2, 3 gives 10, 10, 10). -/

namespace Belay.Sqlite.Model

/-- The scope of a write's table with the catalog position of the table: the table is the first source
of the scope. -/
def Scope.withTablePosition (position : Nat) : Scope → Scope
  | [] => []
  | table :: rest => { table with catalogPosition := some position } :: rest

/-- Complete the resolution of a write to a view ({name}`resolveViewTarget`) with the names of the
write. -/
def resolveViewTargetTraced (context : ResolveContext) (catalog : Catalog) (view : Identifier)
    (written : TracedResolution) : TracedResolution :=
  ⟨resolveViewTarget context catalog view written.drop, written.trace⟩

/-- Resolve the subqueries of a write to the table {lit}`tableName`, whose syntax holds them at
child {lit}`field`, around the scope that {lit}`scopeOf` gives for the table, then the write
with them ({lit}`resolveWrite`). The optional {lit}`columnNames` supplies explicit CTE/view
output names; use the empty default for ordinary subqueries. Optional {lit}`viewRoots`
identify stored definitions whose outer names and column counts need view checks. A subquery that reads the written table directly is
{name}`RestrictionKind.subqueryReadsTarget`. A view target is not
writable: its subqueries are not resolved, so that they cannot give an error before the error of
the view, and the write itself reports that error ({name}`resolveViewTarget`). The trace holds the
names of the subqueries, each once ({name}`Traced.settle`), then those of the write. -/
def resolveWriteSubqueriesTraced (context : ResolveContext) (catalog : Catalog) (field : Nat)
    (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : List Resolved.Query → SubqueryShapes → TracedResolution)
    (columnNames : List (Nat × List Identifier) := []) (viewRoots : List (Nat × Identifier) := []) :
    TracedResolution :=
  if (catalog.findView tableName).isSome then resolveViewTargetTraced context catalog tableName (resolveWrite [] {}) else
  let target := catalog.findTable tableName
  let scope := (target.map fun (position, table) => (scopeOf table).withTablePosition position).getD []
  Traced.sourceStage catalog (resolveSubqueriesTraced context.profile.dqsDml catalog field (QueryScope.ofScope scope)
      subqueries columnNames viewRoots).settle fun (resolved, shapes) =>
    if target.any fun (position, _) => resolved.any (·.readsTable position) then
      Traced.lift (restrict [field] .subqueryReadsTarget)
    else resolveWrite resolved { later := shapes }

/-- The resolution of a write with its subqueries: {name}`resolveWriteSubqueriesTraced` without its
trace, for a write that has none. -/
def resolveWriteSubqueries (context : ResolveContext) (catalog : Catalog) (field : Nat) (tableName : Identifier)
    (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : List Resolved.Query → SubqueryShapes → StatementResolution)
    (columnNames : List (Nat × List Identifier) := []) (viewRoots : List (Nat × Identifier) := []) :
    StatementResolution :=
  (resolveWriteSubqueriesTraced context catalog field tableName scopeOf subqueries
    (fun resolved shapes => Traced.lift (resolveWrite resolved shapes)) columnNames viewRoots).drop

/-- The scope of the written table of {lit}`UPDATE` and {lit}`DELETE`, as their expressions see it. -/
def writtenScope (tableName : Identifier) (table : CatalogTable) : Scope :=
  Scope.single tableName table.columns !table.withoutRowid

end Belay.Sqlite.Model
