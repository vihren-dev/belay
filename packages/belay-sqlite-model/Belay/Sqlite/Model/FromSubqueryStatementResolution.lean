import Belay.Sqlite.Model.FromSubquerySelectResolution

set_option doc.verso true

/-! The resolution of a statement {lit}`SELECT p1, … FROM t WHERE c(q)` of one table with one correlated subquery
{lit}`q` of another table (task 20261027), as lemmas about {lit}`resolveStatement` for a catalog that has both tables.
The parts that depend on the names (the result columns, the condition and the columns of the subquery) are
hypotheses, as in {lit}`resolveStatement_selectOne_subquery`: the catalog is free, so a proof of a claim over every
database gives them from the columns that it assumes. -/

namespace Belay.Sqlite.Model

/-- The scope of a subquery of one table inside a query of one table: the scope {lit}`outer` of the query around it,
one depth further out, followed by the scope {lit}`inner` of its own table, whose first cell is at {lit}`start`, the
number of cells of the query around it. It is the scope that {lit}`resolveSelect` gives the subquery, for the scopes of two
tables that the catalog has ({name}`tableScope`). -/
def correlatedScope (outer inner : Scope) (start : Nat) : Scope :=
  Scope.enclose outer (inner.map fun source => { source with offset := start })

/-- The scope of a table that the catalog has at a position has the columns of the table, so its width is the number of
columns. Proof sketch: the definitions compute ({name}`Scope.columns_singleAt`). -/
theorem tableScope_columns_length (catalog : Catalog) (reference : Syntax.TableReference) (position : Nat)
    (table : CatalogTable) : (tableScope catalog reference position table).columns.length = table.columns.length := by
  simp [tableScope, Scope.columns_singleAt]

/-- For every statement {lit}`SELECT p1, … FROM t WHERE c(q)` of a table {lit}`t` with one subquery
{lit}`SELECT r1, … FROM u WHERE d` of a table {lit}`u`, with tables that the catalog of the state has at positions,
without table-function arguments and indexed queries, whose result columns call no aggregate and have no star issue,
and whose parts resolve (the result columns and the condition of the statement in the scope of {lit}`t` with the shape
of the subquery, the result columns and the condition of the subquery in the scope {name}`correlatedScope`, with the
width {lit}`outer` of a row of {lit}`t`, and no fallible call consumes an aggregate value), resolution gives the simple
query of the first source of {lit}`t` with the condition and result columns of the statement, and the one subquery: the
simple query of the first source of {lit}`u` with the width {lit}`outer`, its condition and its result columns. It
leaves the state as it is. The shape of the subquery is the one that the resolver gives ({lit}`shapeIs`). The table
references name no schema: neither is a {lit}`before.t` source. Proof sketch: {name}`resolveStatement_select_of_resolveSelect`
and {name}`resolveSelect_from_one_subquery`; the table {lit}`t` resolves by {name}`resolveSources_table`, the table
{lit}`u` after the cells of {lit}`t` by {name}`resolveSources_table_after`, the subquery body by
{name}`resolveQueryBody_simple_outer` and the body of the statement by {name}`resolveQueryBody_simple`. -/
theorem resolveStatement_selectFrom_subquery (context : ResolveContext) (state : ResolveState)
    (mainReference innerReference : Syntax.TableReference) (mainColumns innerColumns : List Syntax.ResultColumn)
    (mainFilter : Syntax.Expr) (innerFilter : Option Syntax.Expr) (position innerPosition outer : Nat)
    (table innerTable : CatalogTable)
    (mainNamed : mainReference.query = none) (mainSchema : mainReference.schema = none)
    (mainArguments : mainReference.arguments = none)
    (mainFound : state.catalog.findTable mainReference.table = some (position, table))
    (innerNamed : innerReference.query = none) (innerSchema : innerReference.schema = none)
    (innerArguments : innerReference.arguments = none)
    (innerFound : state.catalog.findTable innerReference.table = some (innerPosition, innerTable))
    (outerIs : table.columns.length = outer) (outerScope innerScope : Scope)
    (outerScopeIs : outerScope = tableScope state.catalog mainReference position table)
    (innerScopeIs : innerScope = tableScope state.catalog innerReference innerPosition innerTable)
    (mainPlain : (mainColumns.all fun
      | .expression value _ _ => value.aggregateCalls.isEmpty
      | .star | .sourceStar _ => true) = true)
    (innerPlain : (innerColumns.all fun
      | .expression value _ _ => value.aggregateCalls.isEmpty
      | .star | .sourceStar _ => true) = true)
    (mainNoStar : starIssue outerScope mainColumns = none)
    (innerNoStar : starIssue (correlatedScope outerScope
      innerScope outer) innerColumns = none)
    (innerResolved : List (List (Resolved.Output × String × Option Affinity))) (innerCondition : Option Resolved.Expr)
    (innerColumnsOk : resolveAll (resolveResultColumn context.profile.dqsDml
      (correlatedScope outerScope
        innerScope outer)
      { current := some 0, outer }) innerColumns = .ok innerResolved)
    (innerFilterOk : FilterResolves context.profile.dqsDml
      (correlatedScope outerScope
        innerScope outer)
      ((resultAliases (correlatedScope outerScope
        innerScope outer) innerColumns).filterMap id ++
        (resultAliases outerScope mainColumns).filterMap id)
      innerFilter innerCondition { current := some 0, outer })
    (innerNoFeed : (innerResolved.flatten.filterMap fun (output, _) => match output with
      | .scalar expression => some expression
      | .aggregate _ => none).any (fun expression =>
        expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false)
    (shape : SubqueryShape)
    (shapeIs : shape = subqueryShape (correlatedScope outerScope
      innerScope outer) { current := some 0, outer }
      (Syntax.Subquery.mk innerColumns (some innerReference) [] innerFilter [] [] none none none none false none none)
      { Resolved.Query.simple [Resolved.QuerySource.first innerPosition] innerCondition
        (innerResolved.flatten.map (·.1)) (innerResolved.flatten.map (·.2.1)) with outer }
      (innerResolved.flatten.head?.bind (·.2.2)))
    (mainResolved : List (List (Resolved.Output × String × Option Affinity))) (mainCondition : Resolved.Expr)
    (mainColumnsOk : resolveAll (resolveResultColumn context.profile.dqsDml
      outerScope { later := [shape] }) mainColumns = .ok mainResolved)
    (mainFilterOk : FilterResolves context.profile.dqsDml outerScope
      ((resultAliases outerScope mainColumns).filterMap id)
      (some mainFilter) (some mainCondition) { later := [shape] })
    (mainNoFeed : (mainResolved.flatten.filterMap fun (output, _) => match output with
      | .scalar expression => some expression
      | .aggregate _ => none).any (fun expression =>
        expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false) :
    resolveStatement context state (.select mainColumns (some mainReference) [] (some mainFilter) [] [] none none
        [Syntax.Subquery.mk innerColumns (some innerReference) [] innerFilter [] [] none none none none false none none]
        none false none) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.first position] (some mainCondition)
          (mainResolved.flatten.map (·.1)) (mainResolved.flatten.map (·.2.1)))
        [{ Resolved.Query.simple [Resolved.QuerySource.first innerPosition] innerCondition
          (innerResolved.flatten.map (·.1)) (innerResolved.flatten.map (·.2.1)) with outer }], state) := by
  subst outerIs outerScopeIs innerScopeIs
  unfold correlatedScope at innerNoStar innerColumnsOk innerFilterOk shapeIs
  have simpleMain : (Syntax.Subquery.mk mainColumns (some mainReference) [] (some mainFilter) [] [] none none none none
      false none none).Simple := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, mainPlain⟩
  have simpleInner : (Syntax.Subquery.mk innerColumns (some innerReference) [] innerFilter [] [] none none none none
      false none none).Simple := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, innerPlain⟩
  have innerBody := resolveQueryBody_simple_outer context.profile.dqsDml
    (Scope.enclose (tableScope state.catalog mainReference position table)
      ((tableScope state.catalog innerReference innerPosition innerTable).map fun source =>
        { source with offset := table.columns.length }))
    (some 0) [] table.columns.length ((resultAliases (tableScope state.catalog mainReference position table)
      mainColumns).filterMap id) _ _ simpleInner _ innerCondition _ innerColumnsOk innerFilterOk
    (resolvePendingSources_table _ _ innerPosition) innerNoFeed
  have mainBody := resolveQueryBody_simple context.profile.dqsDml (tableScope state.catalog mainReference position table)
    none [shape] [] _ _ simpleMain _ (some mainCondition) _ mainColumnsOk (by simpa using mainFilterOk)
    (resolvePendingSources_table _ _ position) mainNoFeed
  have innerSources := resolveSources_table_after state.catalog innerReference innerPosition innerTable
    table.columns.length innerNamed innerSchema innerArguments innerFound
  refine resolveStatement_select_of_resolveSelect context state
    (Syntax.Subquery.mk mainColumns (some mainReference) [] (some mainFilter) [] [] none none none none false none none)
    _ rfl rfl _ ?_
  refine resolveSelect_from_one_subquery context state.catalog
    (Syntax.Subquery.mk mainColumns (some mainReference) [] (some mainFilter) [] [] none none none none false none none)
    (Syntax.Subquery.mk innerColumns (some innerReference) [] innerFilter [] [] none none none none false none none)
    position rfl rfl rfl rfl rfl _
    (resolveSources_table state.catalog mainReference position table mainNamed mainSchema mainArguments mainFound
      (sourceExpansion state.catalog 8 _ none)) mainNoStar _ _
    (by rw [tableScope_columns_length state.catalog mainReference position table]; exact innerSources) innerNoStar
    { Resolved.Query.simple [Resolved.QuerySource.first innerPosition] innerCondition
      (innerResolved.flatten.map (·.1)) (innerResolved.flatten.map (·.2.1)) with outer := table.columns.length }
    (innerResolved.flatten.head?.bind (·.2.2)) ?_ shape ?_
    (Resolved.Query.simple [Resolved.QuerySource.first position] (some mainCondition)
      (mainResolved.flatten.map (·.1)) (mainResolved.flatten.map (·.2.1)))
    (mainResolved.flatten.head?.bind (·.2.2)) ?_ rfl
  · simpa [tableScope_columns_length] using innerBody
  · simpa [tableScope_columns_length] using shapeIs
  · simpa using mainBody

end Belay.Sqlite.Model
