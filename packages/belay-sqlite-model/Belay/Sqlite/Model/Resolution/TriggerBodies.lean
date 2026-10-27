import Belay.Sqlite.Model.Resolution.CommonTableWrites
import Belay.Sqlite.Model.Resolution.SelectResolution
import Belay.Sqlite.Model.Resolution.TriggerRaise
import Belay.Sqlite.Model.Resolution.ViewColumns
import Belay.Sqlite.Model.StatementClock

set_option doc.verso true

/-! Resolution of the statements of a trigger's body (ADR 0018, D5) with the resolvers of the
statements of the same name, over the trigger's rows ({name}`Belay.Sqlite.Model.TriggerRow`). A
restriction of a body is a restriction of the write whose resolution resolves the trigger. A
{lit}`RAISE` that stays in a statement is SQLite's prepare error {lit}`RAISE() may only be used within a trigger-program`
there, and so the restriction of a {lit}`RAISE` form here. -/

namespace Belay.Sqlite.Model

/-- A restriction of a trigger of the write, at the write's statement node. -/
def triggerRestriction (kind : RestrictionKind) : NodeRestriction := { path := [], kind }

/-- The step of a query of a body: a restriction of a trigger form when an expression of it calls
a connection counter ({name}`Resolved.Expr.isCounter`), whose value inside a program the model
does not describe (ADR 0024, D2). -/
def queryStep (step : Resolved.Step) : Except NodeRestriction (Except PrepareError Resolved.Step) :=
  if step.expressions.any (·.any Resolved.Expr.isCounter) then .error (triggerRestriction .triggerForm)
  else .ok (.ok step)

/-- The step of a write of a body: a restriction of a trigger form when an expression of it has a
call that can fail ({name}`Resolved.Expr.isFallibleCall`), whose failure the row engine does not
describe, or a call of a connection counter, as for {name}`queryStep`. -/
def writeStep (step : Resolved.Step) : Except NodeRestriction (Except PrepareError Resolved.Step) :=
  if step.expressions.any (·.any Resolved.Expr.isFallibleCall) then .error (triggerRestriction .triggerForm)
  else queryStep step

/-- The step of a resolved body statement, its prepare error, or a restriction. -/
def bodyStep : StatementResolution → Except NodeRestriction (Except PrepareError Resolved.Step)
  | .error restriction => .error restriction
  | .ok (.prepareError error, _) =>
    if error == .expression .raiseOutsideTrigger then .error (triggerRestriction .raiseForm) else .ok (.error error)
  | .ok (.insert table rows _ subqueries _, _) => writeStep (.insert table rows [] none subqueries)
  | .ok (.upsert table rows clauses _ algorithm subqueries _, _) => writeStep (.insert table rows clauses algorithm subqueries)
  | .ok (.update table assignments filter _ subqueries _, _) => writeStep (.update table assignments filter subqueries)
  | .ok (.delete table filter _ subqueries _, _) => writeStep (.delete table filter subqueries)
  | .ok (.query query subqueries, _) => queryStep (.query query subqueries)
  | .ok (.createTable .., _) | .ok (.createView .., _) | .ok (.createIndex .., _) | .ok (.createTrigger .., _) | .ok (.addColumn .., _)
  | .ok (.insertSelect .., _) | .ok (.drop .., _) | .ok (.rewrite _, _) | .ok (.dropColumn .., _) | .ok (.begin, _) | .ok (.commit, _) | .ok (.rollback, _) | .ok (.setting .., _) =>
    .error (triggerRestriction .triggerForm)

/-- The step of a resolved body statement with the trace of the resolution:
{name}`bodyStep` of the outcome, and the names that were decided. -/
def bodyStepTraced (resolution : TracedResolution) : Traced NodeRestriction (Except PrepareError Resolved.Step) :=
  ⟨bodyStep resolution.drop, resolution.trace⟩

/-- Resolve a SELECT of a trigger's body as {lit}`resolveSelect` does, with the trigger's rows as
the outer cells of its query, before the cells of its own sources, as a subquery has them.
Nested WITH and stored views use the same indexed expansion. View bodies retain
trigger names while hiding ordinary caller names. The trace holds the names that were decided,
at the paths of the SELECT as written, also when the resolution fails. -/
def resolveBodySelectTraced (context : ResolveContext) (catalog : Catalog) (row : TriggerRow)
    (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) : TracedResolution :=
  let dqs := context.profile.dqsDml
  let resolved : Traced SourceIssue (Resolved.Query × List Resolved.Query) := do
    let expanded ← prepareQuerySourcesTraced catalog 8 query subqueries
    let query := expanded.query
    let subqueries := expanded.copies.queries.toList
    let columnNames := expanded.copies.columnNames
    let viewRoots := expanded.copies.viewRoots
    let result : Traced SourceIssue (Resolved.Query × List Resolved.Query) := do
      let (pending, inner) ← resolveSourcesTraced catalog query.source query.joins row.width
        (fun index => sourceExpansion catalog 8 subqueries none index columnNames)
      let scope := Scope.enclose (row.scope 0) inner
      let main : QueryScope := { scope, pending, outer := row.width, outerAliases := [],
                                 aliases := (resultAliases scope query.columns).filterMap id }
      let (resolvedSubqueries, shapes) ← resolveSubqueriesTraced dqs catalog 8 main subqueries columnNames viewRoots
      let main ← (main.refreshTraced catalog shapes query).mapError .value
      let (resolvedQuery, _) ← (resolveQueryBodyTraced dqs main.scope { later := shapes, outer := row.width } []
        main.pending query).mapError .value
      if let some issue := expanded.copies.recursionIssue 8 resolvedSubqueries then throw (.value issue)
      pure (resolvedQuery, resolvedSubqueries)
    (result.settle.mapError (expanded.copies.originalIssue 8)).mapOccurrences (expanded.copies.originalOccurrence 8)
  ⟨match resolved.drop with
    | .ok (resolvedQuery, resolvedSubqueries) => .ok (.query resolvedQuery resolvedSubqueries, catalog)
    | .error (.noSuchTable name) => prepareError catalog (.noSuchTable name)
    | .error (.value issue) => issueResolution catalog [] issue, resolved.trace⟩

/-- Resolve a SELECT of a trigger's body: {name}`resolveBodySelectTraced` without its trace. -/
def resolveBodySelect (context : ResolveContext) (catalog : Catalog) (row : TriggerRow)
    (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) : StatementResolution :=
  (resolveBodySelectTraced context catalog row query subqueries).drop

/-- Whether a query of a raising SELECT is one that the model evaluates: no source, no
aggregate, no grouping, order, window, {lit}`HAVING` or {lit}`DISTINCT`, no subquery and no call
that can fail, so its one row raises in a known order. -/
def raiseQueryPlain (query : Resolved.Query) (subqueries : List Resolved.Query) : Bool :=
  query.sources.isEmpty && !query.aggregate && query.groupBy.isEmpty && query.orderBy.isEmpty && query.limit.isNone &&
    query.offset == 0 && query.having.isNone && query.distinct.isNone && subqueries.isEmpty &&
    !query.expressions.any (·.any Resolved.Expr.isFallibleCall)

end Belay.Sqlite.Model
