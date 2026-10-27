import Belay.Sqlite.Model.FromSourceResolution
import Belay.Sqlite.Model.SubquerySelectResolution
import Belay.Sqlite.Model.QuerySourceCopyLaws

set_option doc.verso true

/-! The resolution of a {lit}`SELECT` of one table with one correlated subquery (task 20261027): the statement
{lit}`SELECT e FROM t WHERE c(q)` where the subquery {lit}`q` has a table of its own and reads the cells of the row of
{lit}`t`. Resolution resolves the table {lit}`t` first. The scope of {lit}`q` encloses the scope of {lit}`t`, and the
table of {lit}`q` comes after the cells of {lit}`t`. As {lit}`resolveSelect_noFrom_one_subquery` does for a statement
without {lit}`FROM`, the lemma takes the resolutions of the parts as hypotheses, because the catalog is free. -/

namespace Belay.Sqlite.Model

/-- For every {lit}`SELECT` of one table (one source, no joins, no compound) with one subquery that has no parent, no
compound and no WITH declaration, whose table resolves to the scope {lit}`mainScope` and whose own sources resolve after
the cells of {lit}`mainScope`, whose result columns have no star issue in their scopes, whose subquery body resolves in the
scope that encloses {lit}`mainScope` with the width of the outer row, and whose own body resolves with the shape of that
subquery, resolution gives the query and the one resolved subquery, and leaves the catalog as it is. The query of the
statement has a source, so the check of fallible calls does not apply to it. Proof sketch: as for
{name}`resolveSelect_noFrom_one_subquery`, with a main scope that has cells: the width of the subquery is the number of
cells of {lit}`mainScope`; the refresh of the scopes does nothing because no shape has a derived source; the check of
fallible calls passes because the query has a source. -/
theorem resolveSelect_from_one_subquery (context : ResolveContext) (catalog : Catalog) (main sub : Syntax.Subquery)
    (position : Nat) (mainNoJoins : main.joins = []) (mainNoCompound : main.compound = none)
    (parentless : sub.parent = none) (subNoCompound : sub.compound = none) (ordinary : sub.commonTable = none)
    (mainScope : Scope)
    (mainSources : resolveSources catalog main.source main.joins 0 (sourceExpansion catalog 8 [sub] none) =
      .ok ([{ item := .table position, kind := .inner, condition := .none }], mainScope))
    (mainNoStar : starIssue mainScope main.columns = none)
    (subPending : List PendingSource) (subInner : Scope)
    (subSources : resolveSources catalog sub.source sub.joins mainScope.columns.length = .ok (subPending, subInner))
    (subNoStar : starIssue (Scope.enclose mainScope subInner) sub.columns = none)
    (subQuery : Resolved.Query) (affinity : Option Affinity)
    (subBody : resolveQueryBody context.profile.dqsDml (Scope.enclose mainScope subInner)
      { current := some 0, outer := mainScope.columns.length }
      ((resultAliases mainScope main.columns).filterMap id) subPending sub = .ok (subQuery, affinity))
    (shape : SubqueryShape) (shapeIs : shape = subqueryShape (Scope.enclose mainScope subInner)
      { current := some 0, outer := mainScope.columns.length } sub subQuery affinity)
    (mainQuery : Resolved.Query) (mainAffinity : Option Affinity)
    (mainBody : resolveQueryBody context.profile.dqsDml mainScope { later := [shape] } []
      [{ item := .table position, kind := .inner, condition := .none }] main = .ok (mainQuery, mainAffinity))
    (sourced : mainQuery.sources.isEmpty = false) :
    resolveSelect context catalog main [sub] = .ok (.query mainQuery [subQuery], catalog) := by
  have order : scopeOrder none [sub] 2 none = [0] := by
    simp [scopeOrder, parentless, compoundOf]
  have noFallible : (mainQuery.sources.isEmpty && mainQuery.expressions.any (·.any Resolved.Expr.isFallibleCall)) =
      false := by simp [sourced]
  have unique : ([0] : List Nat).eraseDups = [0] := rfl
  have noSource : (subqueryShape (Scope.enclose mainScope subInner) { current := some 0, outer := mainScope.columns.length }
      sub subQuery affinity).source = none := rfl
  have mainNoView := resolveSources_noView catalog main.source main.joins 0 _ [] _ mainScope mainSources
  have subNoView := resolveSources_noView catalog sub.source sub.joins _ _ [] subPending subInner subSources
  have noCopies : querySourceCopiesNeeded catalog main [sub] = false := by
    simp only [querySourceCopiesNeeded, ordinary, Option.isSome_none, List.any_cons, List.any_nil, Bool.or_false,
      Bool.false_or, Bool.or_eq_false_iff]
    exact ⟨mainNoView, subNoView⟩
  subst shapeIs
  simp only [mainNoJoins] at mainSources
  unfold resolveSelect resolveSelectTraced resolveSelectDetailsTraced
  simp [prepareQuerySourcesTraced, resolveSourcesTraced_drop, resolveQueryBodyTraced_drop, traced_drop, noCopies,
    CommonTableCopies.recursionIssue, compoundColumnsIssue, mainSources, mainNoJoins, mainNoCompound, mainNoStar,
    subqueryScopesTraced, order, subqueryScopeTraced, parentless, subSources, subNoStar, resolveSubqueryBodiesTraced,
    subqueryBodyOrder, QueryScope.sourceIndexes, QueryScope.refreshTraced, Scope.refreshSources, unique, noSource,
    subNoCompound, subBody, mainBody, noFallible, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure,
    compoundOf]

end Belay.Sqlite.Model
