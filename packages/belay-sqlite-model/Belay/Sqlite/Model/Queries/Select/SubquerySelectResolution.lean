import Belay.Sqlite.Model.Queries.Select.SimpleStatementResolution
import Belay.Sqlite.Model.Queries.Select.SubqueryExprResolutionLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every {lit}`SELECT` without {lit}`FROM`, joins and compound, with one subquery that has no parent
and no compound or WITH declaration, whose sources and body resolve, and whose own body resolves with the shape of that
subquery, and whose resolved expressions have no fallible call, resolution gives the statement's
query and the one resolved subquery, and leaves the catalog as it is. Proof sketch: unfold the resolver; the
statement's own scope is empty, so the scopes of the subquery are its own scope and the order of the
subqueries is the one subquery; the body of the subquery resolves as hypothesised and its shape is the one that the
statement's body reads; the check of fallible calls in a statement with a subquery passes because
the statement's expressions have none. -/
theorem resolveSelect_noFrom_one_subquery (context : ResolveContext) (catalog : Catalog) (main sub : Syntax.Subquery)
    (mainNoFrom : main.source = none) (mainNoJoins : main.joins = []) (mainNoCompound : main.compound = none)
    (mainNoStar : starIssue [] main.columns = none)
    (parentless : sub.parent = none) (subNoCompound : sub.compound = none)
    (ordinary : sub.commonTable = none)
    (pending : List PendingSource) (inner : Scope)
    (subSources : resolveSources catalog sub.source sub.joins = .ok (pending, inner))
    (subNoStar : starIssue inner sub.columns = none)
    (subQuery : Resolved.Query) (affinity : Option Affinity)
    (subBody : resolveQueryBody context.profile.dqsDml inner { current := some 0 }
      ((resultAliases [] main.columns).filterMap id) pending sub = .ok (subQuery, affinity))
    (shape : SubqueryShape) (shapeIs : shape = subqueryShape inner { current := some 0 } sub subQuery affinity)
    (mainQuery : Resolved.Query) (mainAffinity : Option Affinity)
    (mainBody : resolveQueryBody context.profile.dqsDml [] { later := [shape] } [] [] main = .ok (mainQuery, mainAffinity))
    (plain : mainQuery.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true) :
    resolveSelect context catalog main [sub] = .ok (.query mainQuery [subQuery], catalog) := by
  have order : scopeOrder none [sub] 2 none = [0] := by
    simp [scopeOrder, parentless, compoundOf]
  have noFallible : (mainQuery.sources.isEmpty && mainQuery.expressions.any (·.any Resolved.Expr.isFallibleCall)) = false := by
    simp only [List.all_eq_true, Bool.not_eq_true'] at plain
    simp [List.any_eq_false.mpr fun expression member => by simpa using plain expression member]
  have noMain : resolveSources catalog none [] 0 (sourceExpansion catalog 8 [sub] none) = .ok ([], []) := rfl
  have unique : ([0] : List Nat).eraseDups = [0] := rfl
  have noSource : (subqueryShape inner { current := some 0 } sub subQuery affinity).source = none := rfl
  have subNoView := resolveSources_noView catalog sub.source sub.joins 0 _ [] pending inner subSources
  have noCopies : querySourceCopiesNeeded catalog main [sub] = false := by
    simpa [querySourceCopiesNeeded, Syntax.TableReference.namesStoredView, ordinary, mainNoFrom] using subNoView
  subst shapeIs
  unfold resolveSelect resolveSelectTraced resolveSelectDetailsTraced
  simp [prepareQuerySourcesTraced, resolveSourcesTraced_drop, resolveQueryBodyTraced_drop, traced_drop, noCopies, ordinary, CommonTableCopies.recursionIssue, CommonTableCopies.originalIssue, compoundColumnsIssue, noMain, mainNoFrom, mainNoJoins, mainNoCompound, mainNoStar, subqueryScopes, subqueryScopesTraced, order, subqueryScope, subqueryScopeTraced,
    parentless, Scope.columns, Scope.enclose, subSources, subNoStar, resolveSubqueryBodies, resolveSubqueryBodiesTraced, subqueryBodyOrder, QueryScope.sourceIndexes, QueryScope.refresh, QueryScope.refreshTraced, Scope.refreshSources,
    unique, noSource, subNoCompound, subBody,
    mainBody, noFallible, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure, compoundOf]

end Belay.Sqlite.Model
