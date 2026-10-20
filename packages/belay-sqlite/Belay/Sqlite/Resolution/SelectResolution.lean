import Belay.Sqlite.Resolution.SubqueryResolution

set_option doc.verso true

/-! Resolution of a {lit}`SELECT` statement with its subqueries (ADR 0018, D1): the sources of
its query, its subqueries ({lit}`SubqueryResolution`), whose syntax is at child 8 of
{lit}`Syntax.Statement.select`, and then the body of its query. -/

namespace Belay.Sqlite

/-- Resolve a {lit}`SELECT` with its subqueries: the statement's
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
    let (resolvedSubqueries, shapes) ← resolveSubqueries dqs catalog 8 main subqueries
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
