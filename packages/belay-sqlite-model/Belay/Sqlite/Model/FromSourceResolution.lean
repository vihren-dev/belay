import Belay.Sqlite.Model.SimpleSourceResolution
import Belay.Sqlite.Model.SubqueryExprResolutionLaws

set_option doc.verso true

/-! The resolution of the parts of a simple {lit}`SELECT` of one table that sits around or inside a correlated
subquery (task 20261027): the {lit}`FROM` clause of a table whose cells come after the cells of the query around it,
and the body of a simple query whose row starts with the cells of the query around it. These are the forms of the
subquery in {lit}`SELECT … FROM t WHERE x NOT IN (SELECT c FROM u)`. -/

namespace Belay.Sqlite.Model

/-- A {lit}`FROM` clause that names one table, with no table-function arguments and no joins, resolves when the
catalog has the table, also when its cells come after {lit}`start` cells of a query around it: it gives one inner source
on the catalog position of the table, and the scope of the table ({name}`tableScope`) with its first cell at
{lit}`start`. With {lit}`start = 0` it is {name}`resolveSources_table`. The source reference has no indexed query and
names no schema. Proof sketch: as for {name}`resolveSources_table`; the placement of the source sets its offset to
{lit}`start`. -/
theorem resolveSources_table_after (catalog : Catalog) (reference : Syntax.TableReference) (position : Nat)
    (table : CatalogTable) (start : Nat) (namedSource : reference.query = none) (current : reference.schema = none)
    (arguments : reference.arguments = none) (found : catalog.findTable reference.table = some (position, table))
    (queries : Nat → Except SourceIssue ScopeSource := fun _ => .error (.value (.restriction [] .subqueryHere)))
    (prefix_ : List Nat := []) :
    resolveSources catalog (some reference) [] start queries prefix_ =
      .ok ([{ item := .table position, kind := .inner, condition := .none }],
        (tableScope catalog reference position table).map fun source => { source with offset := start }) := by
  simp [resolveSources_some, resolveReference, resolveReferenceTraced, namedSource, current, arguments,
    resolveTableReferenceTraced, found, maximumJoinTables, Scope.place, mergeJoins, mergeJoinsTraced, traced_drop,
    resolveAll, resolveAllFrom, Bind.bind, Except.bind, Except.mapError, joinOperator, tableScope, Scope.singleAt]

/-- For every simple query ({name}`Syntax.Subquery.Simple`) as in {name}`resolveQueryBody_simple`, but resolved as the
subquery of a query whose row has {lit}`outer` cells (the field {lit}`outer` of {name}`SubqueryShapes`), the body resolves
to the same simple resolved query with that width of the outer row. Proof sketch: the proof of
{name}`resolveQueryBody_simple`; the width of the outer row only sets the field {lit}`outer` of the query, and it
decides nothing for a query without aggregate. -/
theorem resolveQueryBody_simple_outer (dqs : Bool) (scope : Scope) (current : Option Nat) (later : List SubqueryShape) (outer : Nat)
    (outerAliases : List Identifier) (pending : List PendingSource) (query : Syntax.Subquery)
    (simple : query.Simple) (resolved : List (List (Resolved.Output × String × Option Affinity)))
    (condition : Option Resolved.Expr) (sources : List Resolved.QuerySource)
    (columns : resolveAll (resolveResultColumn dqs scope { current, later, outer }) query.columns = .ok resolved)
    (filter : FilterResolves dqs scope ((resultAliases scope query.columns).filterMap id ++ outerAliases) query.filter condition { current, later, outer })
    (pendingOk : resolvePendingSources dqs scope pending = .ok sources)
    (noFeed : (resolved.flatten.filterMap fun (output, _) => match output with
      | .scalar expression => some expression
      | .aggregate _ => none).any (fun expression =>
        expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false) :
    resolveQueryBody dqs scope { current, later, outer } outerAliases pending query =
      .ok ({ Resolved.Query.simple sources condition (resolved.flatten.map (·.1)) (resolved.flatten.map (·.2.1)) with outer },
           resolved.flatten.head?.bind (·.2.2)) := by
  unfold Resolved.Query.simple
  obtain ⟨noJoins, noGroup, noOrder, noLimit, noOffset, noHaving, notDistinct, -, noAggregate⟩ := simple
  have columnFree : ∀ value alias text, Syntax.ResultColumn.expression value alias text ∈ query.columns →
      value.aggregateCalls = [] := fun value alias text member => by
    simp only [List.all_eq_true] at noAggregate
    simpa [List.isEmpty_iff] using noAggregate _ member
  have noCalls : ∀ g : Syntax.ResultColumn → List Syntax.Expr,
      (∀ value alias text, Syntax.ResultColumn.expression value alias text ∈ query.columns →
        g (.expression value alias text) = []) → g .star = [] → (∀ source, g (.sourceStar source) = []) →
      query.columns.flatMap g = [] := fun g expression star sourceStar =>
    List.flatMap_eq_nil_iff.mpr fun column member => by
      cases column with
      | star => exact star
      | sourceStar source => exact sourceStar source
      | expression value alias text => exact expression value alias text member
  have notAggregate : ∀ g : Syntax.ResultColumn → Bool,
      (∀ value alias text, Syntax.ResultColumn.expression value alias text ∈ query.columns →
        g (.expression value alias text) = false) → g .star = false → (∀ source, g (.sourceStar source) = false) →
      query.columns.any g = false := fun g expression star sourceStar =>
    List.any_eq_false.mpr fun column member => by
      cases column with
      | star => simp [star]
      | sourceStar source => simp [sourceStar source]
      | expression value alias text => simp [expression value alias text member]
  have distinctNil : Syntax.Expr.distinctList [] = [] := rfl
  rw [resolveQueryBody_arm]
  simp only [aliasJoinItem?, noJoins, List.zipIdx_nil, List.find?_nil, Option.map_none, noGroup, noOrder, noLimit, noOffset, noHaving, notDistinct]
  rw [notAggregate _ ?flagColumn rfl (fun _ => rfl)]
  simp only [List.isEmpty_nil, Bool.not_true, Bool.or_false, Bool.false_and, Option.toList_none, List.flatMap_nil,
    List.append_nil, ite_false, Bool.false_eq_true]
  rw [noCalls _ ?callColumn rfl (fun _ => rfl)]
  simp only [distinctNil]
  simp only [columns, pendingOk]
  rcases filter with ⟨found, rfl⟩ | ⟨term, expression, affinity, found, rfl, names, resolves⟩
  · simp [resolveAll, resolveAllFrom, windowValue, windowSkipsFailure, Bind.bind, Except.bind, pure, Except.pure, found]
    refine (ite_eq_right_of_eq_false _ _ (eq_false fun feed => ?_)).trans rfl
    rw [List.append_nil, List.append_nil] at feed
    exact absurd (feed.symm.trans noFeed) (by simp)
  · simp [resolveAll, resolveAllFrom, windowValue, windowSkipsFailure, Bind.bind, Except.bind, pure, Except.pure, found,
      names, resolves, Model.condition]
    refine (ite_eq_right_of_eq_false _ _ (eq_false fun feed => ?_)).trans rfl
    rw [List.append_nil, List.append_nil] at feed
    exact absurd (feed.symm.trans noFeed) (by simp)
  case flagColumn => intro value alias text member; simp [columnFree value alias text member]
  case callColumn => intro value alias text member; simp [columnFree value alias text member]

end Belay.Sqlite.Model
