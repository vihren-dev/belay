import Belay.Sqlite.Model.Resolution.Queries
import Belay.Sqlite.Model.QueryRun

set_option doc.verso true

/-! Resolution of the subqueries of a statement (ADR 0018, D1). The scopes go outward-in:
the statement's query or write, then each subquery in the order of the list, enclosed by the
scope of the query around it ({name}`Belay.Sqlite.Model.Scope.enclose`), with its cells after the
outer cells. The bodies go inward-out, from the last subquery to the first and then the
statement's own expressions, because an expression needs the shapes of the subqueries that
it names ({name}`Belay.Sqlite.Model.SubqueryShape`). An issue of subquery {lit}`i` is at the path
{lit}`[field, i]` and the path within its clauses, where {lit}`field` is the child of the
statement's syntax that holds its subqueries: 8 for {lit}`SELECT`. -/

namespace Belay.Sqlite.Model

/-- One query of a statement before resolution resolves its body: its scope, its pending
sources, the number of outer cells, and the aliases that its {lit}`WHERE` may name, of the
queries around it and of itself. -/
structure QueryScope where
  /-- The scope of the query, enclosed by those of the queries around it. -/
  scope : Scope
  /-- The sources of {lit}`FROM` whose expressions are not resolved yet. -/
  pending : List PendingSource
  /-- The number of cells of the queries around it. -/
  outer : Nat
  /-- The aliases of the result columns of the queries around it. -/
  outerAliases : List Identifier
  /-- The aliases of its own result columns and of the queries around it. -/
  aliases : List Identifier

/-- A source issue at a path of the statement: a value issue under the path, and a missing
table as it is. -/
def SourceIssue.under (path : List Nat) : SourceIssue → SourceIssue
  | .value issue => .value (issue.under path)
  | .noSuchTable name => .noSuchTable name

/-- The scope of a write's table or of no table, as the scope of the statement around its
subqueries: no pending sources, outer cells or aliases. -/
def QueryScope.ofScope (scope : Scope) : QueryScope :=
  { scope, pending := [], outer := 0, outerAliases := [], aliases := [] }

/-- The scope of subquery {lit}`index` after the scopes of the earlier subqueries: the
sources of its {lit}`FROM` placed after the cells of the query around it, which is the
statement's query or an earlier subquery; else {name}`RestrictionKind.subqueryHere`, which
the frontend never gives. Paths start at {lit}`[field, index]`. -/
def subqueryScope (catalog : Catalog) (field : Nat) (main : QueryScope) (scopes : List QueryScope) (index : Nat)
    (subquery : Syntax.Subquery) : Except SourceIssue QueryScope := do
  let around? := match subquery.parent with
    | none => some main
    | some parent => if parent < index then scopes[parent]? else none
  let some around := around? | throw (.value (.restriction [field, index] .subqueryHere))
  let width := around.scope.columns.length
  let (pending, inner) ← (resolveSources catalog subquery.source subquery.joins width).mapError (·.under [field, index])
  let scope := Scope.enclose around.scope inner
  pure { scope, pending, outer := width, outerAliases := around.aliases,
         aliases := (resultAliases scope subquery.columns).filterMap id ++ around.aliases }

/-- The scopes of the subqueries in the order of the list ({name}`subqueryScope`). -/
def subqueryScopes (catalog : Catalog) (field : Nat) (main : QueryScope) (subqueries : List Syntax.Subquery) :
    Except SourceIssue (List QueryScope) :=
  subqueries.foldlM (fun scopes subquery => (scopes ++ [·]) <$> subqueryScope catalog field main scopes scopes.length subquery)
    []

/-- The shape of a resolved subquery ({name}`SubqueryShape`): the query around it, its number
of result columns, the affinity and collations of its first result column, and the lowest
cell that it or a subquery that it names reads. -/
def subqueryShape (scope : Scope) (shapes : SubqueryShapes) (subquery : Syntax.Subquery) (query : Resolved.Query)
    (affinity : Option Affinity) : SubqueryShape :=
  let (explicitCollation, columnCollation) := firstCollations scope subquery.columns
  { parent := subquery.parent, columns := query.columns.length, affinity, explicitCollation, columnCollation,
    lowest := query.expressions.foldl (fun lowest expression => minPosition lowest (expression.lowestRead shapes)) none }

/-- Resolve the bodies of the subqueries from the last to the first ({name}`resolveQueryBody`),
each with the shapes of the subqueries after it: the resolved subqueries and their shapes, in
the order of the list. Paths start at {lit}`[field, index]`. -/
def resolveSubqueryBodies (dqs : Bool) (field : Nat) (scopes : List QueryScope) (subqueries : List Syntax.Subquery) :
    Except ValueIssue (List Resolved.Query × List SubqueryShape) :=
  ((List.range subqueries.length).zip (scopes.zip subqueries)).foldr (fun (index, around, subquery) later => do
    let (queries, shapes) ← later
    let current : SubqueryShapes := { current := some index, later := shapes, outer := around.outer }
    let (query, affinity) ← (resolveQueryBody dqs around.scope current around.outerAliases around.pending subquery).mapError
      (·.under [field, index])
    pure (query :: queries, subqueryShape around.scope current subquery query affinity :: shapes)) (.ok ([], []))

/-- Resolve the subqueries of a statement around whose own expressions is {lit}`main`: their
scopes ({name}`subqueryScopes`), then their bodies ({name}`resolveSubqueryBodies`), with the
statement's syntax holding them at child {lit}`field`. -/
def resolveSubqueries (dqs : Bool) (catalog : Catalog) (field : Nat) (main : QueryScope)
    (subqueries : List Syntax.Subquery) : Except SourceIssue (List Resolved.Query × List SubqueryShape) := do
  let scopes ← subqueryScopes catalog field main subqueries
  (resolveSubqueryBodies dqs field scopes subqueries).mapError .value

/-- Whether a subquery reads the table at the catalog position directly. -/
def Resolved.Query.readsTable (position : Nat) (query : Resolved.Query) : Bool :=
  query.sources.any (·.source == .table position)

end Belay.Sqlite.Model
