import Belay.Sqlite.Resolution.Queries
import Belay.Sqlite.QueryRun

set_option doc.verso true

/-! Resolution of a {lit}`SELECT` statement with its subqueries (ADR 0018, D1). The scopes go
outward-in: the statement's query, then each subquery in the order of the list, enclosed by
the scope of the query around it ({name}`Belay.Sqlite.Scope.enclose`), with its cells after the outer
cells. The bodies go inward-out, from the last subquery to the first and then the
statement's query, because a query needs the shapes of the subqueries that it names
({name}`Belay.Sqlite.SubqueryShape`). An issue of subquery {lit}`i` is at the path {lit}`[8, i]` and the
path within its clauses, as {lit}`Syntax.Statement.select` holds the subqueries at child 8. -/

namespace Belay.Sqlite

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

/-- The scope of subquery {lit}`index` after the scopes of the earlier subqueries: the
sources of its {lit}`FROM` placed after the cells of the query around it, which is the
statement's query or an earlier subquery; else {name}`RestrictionKind.subqueryHere`, which
the frontend never gives. -/
def subqueryScope (catalog : Catalog) (main : QueryScope) (scopes : List QueryScope) (index : Nat)
    (subquery : Syntax.Subquery) : Except SourceIssue QueryScope := do
  let around? := match subquery.parent with
    | none => some main
    | some parent => if parent < index then scopes[parent]? else none
  let some around := around? | throw (.value (.restriction [8, index] .subqueryHere))
  let width := around.scope.columns.length
  let (pending, inner) ← (resolveSources catalog subquery.source subquery.joins width).mapError (·.under [8, index])
  let scope := Scope.enclose around.scope inner
  pure { scope, pending, outer := width, outerAliases := around.aliases,
         aliases := (resultAliases scope subquery.columns).filterMap id ++ around.aliases }

/-- The scopes of the subqueries in the order of the list ({name}`subqueryScope`). -/
def subqueryScopes (catalog : Catalog) (main : QueryScope) (subqueries : List Syntax.Subquery) :
    Except SourceIssue (List QueryScope) :=
  subqueries.foldlM (fun scopes subquery => (scopes ++ [·]) <$> subqueryScope catalog main scopes scopes.length subquery) []

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
the order of the list. -/
def resolveSubqueryBodies (dqs : Bool) (scopes : List QueryScope) (subqueries : List Syntax.Subquery) :
    Except ValueIssue (List Resolved.Query × List SubqueryShape) :=
  ((List.range subqueries.length).zip (scopes.zip subqueries)).foldr (fun (index, around, subquery) later => do
    let (queries, shapes) ← later
    let current : SubqueryShapes := { current := some index, later := shapes, outer := around.outer }
    let (query, affinity) ← (resolveQueryBody dqs around.scope current around.outerAliases around.pending subquery).mapError
      (·.under [8, index])
    pure (query :: queries, subqueryShape around.scope current subquery query affinity :: shapes)) (.ok ([], []))

/-- Resolve a {lit}`SELECT` with its subqueries, see the module documentation: the statement's
query and its subqueries, or SQLite's {lit}`no such table: %s`, a prepare error or a
restriction. A query without {lit}`FROM` that has a subquery and a call that can fail is
{name}`RestrictionKind.subqueryFallibleCall`. -/
def resolveSelect (context : ResolveContext) (catalog : Catalog) (index : Nat) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) : StatementResolution :=
  let dqs := context.profile.dqsDml
  let resolved : Except SourceIssue (Resolved.Query × List Resolved.Query) := do
    let (pending, scope) ← resolveSources catalog query.source query.joins
    let main : QueryScope := { scope, pending, outer := 0, outerAliases := [],
                               aliases := (resultAliases scope query.columns).filterMap id }
    let scopes ← subqueryScopes catalog main subqueries
    let (resolvedSubqueries, shapes) ← (resolveSubqueryBodies dqs scopes subqueries).mapError .value
    let (resolvedQuery, _) ← (resolveQueryBody dqs scope { later := shapes } [] pending query).mapError .value
    if resolvedQuery.sources.isEmpty && !subqueries.isEmpty &&
        resolvedQuery.expressions.any (·.any Resolved.Expr.isFallibleCall) then
      throw (.value (.restriction [] .subqueryFallibleCall))
    pure (resolvedQuery, resolvedSubqueries)
  match resolved with
  | .ok (resolvedQuery, resolvedSubqueries) => .ok (.query resolvedQuery resolvedSubqueries, catalog)
  | .error (.noSuchTable name) => prepareError catalog (.noSuchTable name)
  | .error (.value issue) => issueResolution catalog index [] issue

/-- For every successful resolution of a {lit}`SELECT`, the catalog is unchanged and the
resolved statement applied to the input catalog gives the input catalog again
({lit}`Resolved.Statement.applyCatalog`); the statement is not transaction control.
Proof sketch: every branch of the resolver returns the input catalog and a query or a
prepare error. -/
theorem resolveSelect_same (context : ResolveContext) (catalog after : Catalog) (index : Nat)
    (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) (statement : Resolved.Statement)
    (ok : resolveSelect context catalog index query subqueries = .ok (statement, after)) :
    after = catalog ∧ statement.applyCatalog catalog = catalog ∧ statement.isControl = false := by
  unfold resolveSelect at ok
  simp only [prepareError, issueResolution] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl, rfl⟩) | (cases ok)

end Belay.Sqlite
