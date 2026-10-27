import Belay.Sqlite.Model.FromSubqueryStatementResolution
import Belay.Sqlite.Model.CorrelatedSubqueryRun

set_option doc.verso true

/-! The resolution of {lit}`SELECT p1, … FROM t WHERE x [NOT] IN (SELECT c FROM u)` (task 20261027): for a catalog
that has both tables, the statement resolves to two queries of one table each ({lit}`Resolved.Query.oneTable`), the
form that the query laws of {lit}`x IN` against {lit}`EXISTS` use. The parts that depend on the names (the result
columns, the probe {lit}`x` and the result column {lit}`c` of the subquery) are hypotheses: the catalog is free, so a
proof of a claim over every database gives them from the columns that it assumes. -/

namespace Belay.Sqlite.Model

/-- For every statement {lit}`SELECT p1, … FROM t WHERE x [NOT] IN (SELECT c FROM u)` of two tables that the catalog of
the state has at positions, without table-function arguments and indexed queries, where the result columns {lit}`p1, …`
call no aggregate, have no star issue, and resolve in the scope of {lit}`t` to scalar projections with names, the probe
{lit}`x` names no alias of a result column and resolves in the scope of {lit}`t` to an expression with an affinity, and
the one result column {lit}`c` of the subquery resolves in the scope {name}`correlatedScope` to a projection with an
affinity and a name, and no fallible call consumes an aggregate value, resolution gives two queries and leaves the state as it is:
* the statement is the query {name}`Resolved.Query.oneTable` of the table {lit}`t` with the width 0, the condition
  {lit}`IN` (or {lit}`NOT IN` when {lit}`negated`) of subquery 0 on the resolved probe, with the comparison affinity of
  the probe and the column ({name}`comparisonAffinity`) and the collation {name}`inCollation` of the probe and the shape of
  the subquery, and the projections of the result columns;
* the one subquery is the query of the table {lit}`u` with the width {lit}`outer` of a row of {lit}`t`, without condition
  and with the projection of {lit}`c`.

The shape of the subquery is the one that the resolver gives ({lit}`shapeIs`). The table references name no schema.
Proof sketch: {name}`resolveStatement_selectFrom_subquery` with the condition from {name}`resolveOperand_inQuery` and
{name}`SubqueryShapes.column_only`; the subquery has no condition, and its column does not name an aggregate. -/
theorem resolveStatement_selectFrom_inQuery (context : ResolveContext) (state : ResolveState)
    (mainReference innerReference : Syntax.TableReference) (mainColumns : List Syntax.ResultColumn)
    (probe innerValue : Syntax.Expr) (innerAlias : Option Identifier) (innerText : String) (negated : Bool)
    (position innerPosition outer : Nat) (table innerTable : CatalogTable) (outerScope innerScope : Scope)
    (mainNamed : mainReference.query = none) (mainSchema : mainReference.schema = none)
    (mainArguments : mainReference.arguments = none)
    (mainFound : state.catalog.findTable mainReference.table = some (position, table))
    (innerNamed : innerReference.query = none) (innerSchema : innerReference.schema = none)
    (innerArguments : innerReference.arguments = none)
    (innerFound : state.catalog.findTable innerReference.table = some (innerPosition, innerTable))
    (outerIs : table.columns.length = outer)
    (outerScopeIs : outerScope = tableScope state.catalog mainReference position table)
    (innerScopeIs : innerScope = tableScope state.catalog innerReference innerPosition innerTable)
    (mainPlain : (mainColumns.all fun
      | .expression value _ _ => value.aggregateCalls.isEmpty
      | .star | .sourceStar _ => true) = true)
    (innerPlain : innerValue.aggregateCalls.isEmpty = true)
    (mainNoStar : starIssue outerScope mainColumns = none)
    (projection : Resolved.Expr) (innerName : String) (columnAffinity : Option Affinity)
    (innerColumnOk : resolveAll (resolveResultColumn context.profile.dqsDml (correlatedScope outerScope innerScope outer)
      { current := some 0, outer }) [.expression innerValue innerAlias innerText] =
        .ok [[(.scalar projection, innerName, columnAffinity)]])
    (innerNoFeed : projection.any (fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false)
    (shape : SubqueryShape)
    (shapeIs : shape = subqueryShape (correlatedScope outerScope innerScope outer) { current := some 0, outer }
      (Syntax.Subquery.mk [.expression innerValue innerAlias innerText] (some innerReference) [] none [] [] none none
        none none false none none)
      (Resolved.Query.oneTable innerPosition outer none [projection] [innerName]) columnAffinity)
    (mainResolved : List (List (Resolved.Output × String × Option Affinity))) (mainProjections : List Resolved.Expr)
    (mainNames : List String) (probeExpression : Resolved.Expr) (probeAffinity : Option Affinity)
    (mainColumnsOk : resolveAll (resolveResultColumn context.profile.dqsDml outerScope { later := [shape] })
      mainColumns = .ok mainResolved)
    (mainOutputs : mainResolved.flatten.map (·.1) = mainProjections.map Resolved.Output.scalar)
    (mainOutputNames : mainResolved.flatten.map (·.2.1) = mainNames)
    (probeOk : resolveOperand context.profile.dqsDml outerScope { later := [shape] } true probe =
      .ok (probeExpression, probeAffinity))
    (probeNoAlias : namesAlias outerScope ((resultAliases outerScope mainColumns).filterMap id) probe = false)
    (mainNoFeed : (mainResolved.flatten.filterMap fun (output, _) => match output with
      | .scalar expression => some expression
      | .aggregate _ => none).any (fun expression =>
        expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false) :
    resolveStatement context state (.select mainColumns (some mainReference) [] (some (.inQuery probe 0 negated)) [] []
        none none [Syntax.Subquery.mk [.expression innerValue innerAlias innerText] (some innerReference) [] none [] []
          none none none none false none none] none false none) =
      .ok (.query (Resolved.Query.oneTable position 0
          (some (.inQuery probeExpression 0 (comparisonAffinity probeAffinity columnAffinity)
            (inCollation outerScope probe shape) negated)) mainProjections mainNames)
        [Resolved.Query.oneTable innerPosition outer none [projection] [innerName]], state) := by
  have parentless : shape.parent = none := by subst shapeIs; rfl
  have single : shape.columns = 1 := by subst shapeIs; rfl
  have affinityIs : shape.affinity = columnAffinity := by subst shapeIs; rfl
  have filterOk : FilterResolves context.profile.dqsDml outerScope
      ((resultAliases outerScope mainColumns).filterMap id) (some (.inQuery probe 0 negated))
      (some (.inQuery probeExpression 0 (comparisonAffinity probeAffinity columnAffinity)
        (inCollation outerScope probe shape) negated)) { later := [shape] } :=
    FilterResolves.of_term (result := (.inQuery probeExpression 0 (comparisonAffinity probeAffinity columnAffinity)
      (inCollation outerScope probe shape) negated, none)) (by simpa [namesAlias] using probeNoAlias)
      (by rw [resolveOperand_inQuery, probeOk, SubqueryShapes.column_only parentless (by subst shapeIs; rfl) single]
          simp [Except.mapError, Bind.bind, Except.bind, affinityIs])
  have result := resolveStatement_selectFrom_subquery context state mainReference innerReference mainColumns
    [.expression innerValue innerAlias innerText] (.inQuery probe 0 negated) none position innerPosition outer table
    innerTable mainNamed mainSchema mainArguments mainFound innerNamed innerSchema innerArguments innerFound outerIs
    outerScope innerScope outerScopeIs innerScopeIs mainPlain (by simpa using innerPlain) mainNoStar (by simp [starIssue]) _ none innerColumnOk
    (FilterResolves.of_none _ _ _ _) (by
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.filterMap_cons, List.filterMap_nil,
        List.any_cons, List.any_nil, Bool.or_false]
      exact innerNoFeed) shape shapeIs mainResolved _
    mainColumnsOk filterOk mainNoFeed
  rw [result, mainOutputs, mainOutputNames]
  rfl

end Belay.Sqlite.Model
