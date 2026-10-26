import Belay.Sqlite.Model.Resolution.SubqueryResolution
import Belay.Sqlite.Model.Resolution.QuerySourceExpansion

set_option doc.verso true

/-! Resolution of a {lit}`SELECT` statement with its subqueries (ADR 0018, D1): the sources of
its query, its subqueries ({lit}`SubqueryResolution`), whose syntax is at child 8 of
{lit}`Syntax.Statement.select`, and then the body of its query, or of its compound from the
terms among its subqueries (ADR 0019, D3). -/

namespace Belay.Sqlite.Model

/-- Resolve a {lit}`SELECT` with its subqueries and retain the refreshed source scope:
its columns supply the same metadata to query execution and catalog observation.
For an ordinary statement use {lit}`resolveSelect`. The result contains the statement's
query and its subqueries, or SQLite's {lit}`no such table: %s`, a prepare error or a
restriction. Used WITH and stored-view definitions are copied before ordinary
resolution; unused definitions do not enter the executable query list. Stored views
resolve against the current catalog and hide ordinary caller names. SQLite expands the {lit}`*` of the statement's query ({name}`starIssue`) before
its subqueries. A compound query resolves from its terms ({name}`resolveCompoundBodyTraced`). A query
without {lit}`FROM`, or a term of the compound without {lit}`FROM`, that has a call that can
fail, in a statement with a subquery that is no term, is
{name}`RestrictionKind.subqueryFallibleCall`. The optional {lit}`initial` is the catalog of the initial database
of a two-state query: a source {lit}`before.t` resolves there ({name}`resolveReferenceTraced`); without it such a
source is {name}`RestrictionKind.initialDatabase`. The occurrences are those of the sources, the
subqueries and the clauses of the query; a name of a copy of a {lit}`WITH` definition or a stored view is
moved to the written statement ({name}`CommonTableCopies.originalOccurrence`), and each name is
recorded once ({name}`NameTrace.settled`). -/
def resolveSelectDetailsTraced (context : ResolveContext) (catalog : Catalog) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) (initial : Option Catalog := none) :
    Traced SourceIssue (Resolved.Query × List Resolved.Query × Scope) :=
  let dqs := context.profile.dqsDml
  do
    let expanded ← prepareQuerySourcesTraced catalog 8 query subqueries initial
    let query := expanded.query
    let subqueries := expanded.copies.queries.toList
    let columnNames := expanded.copies.columnNames
    let viewRoots := expanded.copies.viewRoots
    let result : Traced SourceIssue (Resolved.Query × List Resolved.Query × Scope) := do
      let (pending, scope) ← resolveSourcesTraced catalog query.source query.joins 0
        (fun index => sourceExpansion catalog 8 subqueries none index columnNames initial) [] initial
      if let some issue := starIssue scope query.columns then throw (.value issue)
      let main : QueryScope := { scope, pending, outer := 0, outerAliases := [],
                                 aliases := (resultAliases scope query.columns).filterMap id }
      let scopes ← subqueryScopesTraced catalog 8 main query.compound subqueries columnNames viewRoots initial
      let (resolvedSubqueries, shapes) ← (resolveSubqueryBodiesTraced dqs catalog 8 main query.compound scopes subqueries columnNames viewRoots initial).mapError .value
      let main ← (main.refreshTraced catalog shapes query initial).mapError .value
      let scope := main.scope
      let pending := main.pending
      let scopes := scopes.map fun scope => { scope with scope := scope.scope.refreshSources shapes }
      let body : Traced ValueIssue (Resolved.Query × List Resolved.Query) := match query.compound with
        | some compound => do
          let terms ← compoundTerms 0 none compound (scopes.map QueryScope.scope) subqueries resolvedSubqueries shapes
          pure ((← resolveCompoundBodyTraced dqs 0 query compound terms).1, terms.map CompoundTerm.query)
        | none => do
          let (resolved, _) ← resolveQueryBodyTraced dqs scope { later := shapes } [] pending query
          pure (resolved, [resolved])
      let (resolvedQuery, ran) ← body.mapError SourceIssue.value
      if let some issue := expanded.copies.recursionIssue 8 resolvedSubqueries then throw (.value issue)
      let terms := (query.compound.map Syntax.Compound.terms).getD []
      if (List.range subqueries.length).any (!terms.contains ·) &&
          ran.any fun (ran : Resolved.Query) => ran.sources.isEmpty && ran.expressions.any (·.any Resolved.Expr.isFallibleCall) then
        throw (SourceIssue.value (ValueIssue.restriction [] .subqueryFallibleCall))
      pure (resolvedQuery, resolvedSubqueries, scope)
    (result.settle.mapError (expanded.copies.originalIssue 8)).mapOccurrences (expanded.copies.originalOccurrence 8)

/-- The query, the subqueries and the scope of a {lit}`SELECT`:
{name}`resolveSelectDetailsTraced` without its trace. -/
def resolveSelectDetails (context : ResolveContext) (catalog : Catalog) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) (initial : Option Catalog := none) :
    Except SourceIssue (Resolved.Query × List Resolved.Query × Scope) :=
  (resolveSelectDetailsTraced context catalog query subqueries initial).drop

/-- Resolve a SELECT to its query statement or prepare error, with the input catalog unchanged.
Model restrictions retain their original syntax paths. This uses the same query and source
metadata resolution as {name}`resolveSelectDetailsTraced`; the statement needs only its executable
queries. The trace holds the names that were decided, also when the resolution fails. -/
def resolveSelectTraced (context : ResolveContext) (catalog : Catalog) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) (initial : Option Catalog := none) :
    Traced NodeRestriction (Resolved.Statement × Catalog) :=
  let details := resolveSelectDetailsTraced context catalog query subqueries initial
  ⟨match details.drop with
    | .ok (resolvedQuery, resolvedSubqueries, _) => .ok (.query resolvedQuery resolvedSubqueries, catalog)
    | .error (.noSuchTable name) => prepareError catalog (.noSuchTable name)
    | .error (.value issue) => issueResolution catalog [] issue, details.trace⟩

/-- The statement of a SELECT: {name}`resolveSelectTraced` without its trace. -/
def resolveSelect (context : ResolveContext) (catalog : Catalog) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) (initial : Option Catalog := none) : StatementResolution :=
  (resolveSelectTraced context catalog query subqueries initial).drop

/-- For every successful resolution of a {lit}`SELECT`, the catalog is unchanged and the
resolved statement applied to the input catalog gives the input catalog again
({lit}`Resolved.Statement.applyCatalog`); the statement is not transaction control.
Proof sketch: every branch of the resolver returns the input catalog and a query or a
prepare error. -/
theorem resolveSelect_same (context : ResolveContext) (catalog after : Catalog)
    (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) (statement : Resolved.Statement)
    (ok : resolveSelect context catalog query subqueries = .ok (statement, after)) :
    after = catalog ∧ statement.applyCatalog catalog = catalog ∧ statement.isControl = false := by
  unfold resolveSelect resolveSelectTraced at ok
  dsimp only [Traced.drop] at ok
  simp only [prepareError, issueResolution] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl, rfl⟩) | (cases ok)

end Belay.Sqlite.Model
