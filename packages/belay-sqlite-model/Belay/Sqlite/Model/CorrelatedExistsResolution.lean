import Belay.Sqlite.Model.FromSubqueryStatementResolution
import Belay.Sqlite.Model.CorrelatedSubqueryRun

set_option doc.verso true

/-! The resolution of {lit}`SELECT p1, … FROM t WHERE [NOT] EXISTS (SELECT 1 FROM u WHERE d)` (task 20261027): for a
catalog that has both tables, the statement resolves to two queries of one table each
({lit}`Resolved.Query.oneTable`), the form that the query laws of {lit}`NOT EXISTS` against {lit}`NOT IN` use. The
parts that depend on the names (the result columns and the condition {lit}`d` of the subquery, which reads the cells
of the row of {lit}`t`) are hypotheses: the catalog is free, so a proof of a claim over every database gives them from
the columns that it assumes. -/

namespace Belay.Sqlite.Model

/-- For every statement {lit}`SELECT p1, … FROM t WHERE c(EXISTS (SELECT 1 FROM u WHERE d))` of two tables that the
catalog of the state has at positions, without table-function arguments and indexed queries, where the result columns
{lit}`p1, …` call no aggregate, have no star issue and resolve in the scope of {lit}`t` to scalar projections with names,
the test {lit}`c` of subquery 0 resolves to the condition {lit}`mainCondition` for the shape of the subquery
({name}`FilterResolves`), and the condition {lit}`d` (or its absence) resolves in the scope {name}`correlatedScope` to
{lit}`innerCondition`, resolution gives two queries and leaves the state as it is: the statement is the query
{lit}`Resolved.Query.oneTable` of the table {lit}`t` with the width 0, the condition {lit}`mainCondition` and the
projections of the result columns; the one subquery is the query of the table {lit}`u` with the width {lit}`outer` of a
row of {lit}`t`, the condition {lit}`innerCondition` and the literal one named {lit}`"1"`. The shape of the subquery is
the one that the resolver gives ({lit}`shapeIs`). The table references name no schema. Proof sketch:
{name}`resolveStatement_selectFrom_subquery` with the result column {lit}`1` ({name}`resolveColumns_one`). -/
theorem resolveStatement_selectFrom_existsTest (context : ResolveContext) (state : ResolveState)
    (mainReference innerReference : Syntax.TableReference) (mainColumns : List Syntax.ResultColumn)
    (mainFilter : Syntax.Expr) (innerFilter : Option Syntax.Expr)
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
    (mainNoStar : starIssue outerScope mainColumns = none) (innerCondition : Option Resolved.Expr)
    (innerFilterOk : FilterResolves context.profile.dqsDml (correlatedScope outerScope innerScope outer)
      ((resultAliases outerScope mainColumns).filterMap id) innerFilter innerCondition { current := some 0, outer })
    (shape : SubqueryShape)
    (shapeIs : shape = subqueryShape (correlatedScope outerScope innerScope outer) { current := some 0, outer }
      (Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some innerReference) [] innerFilter [] [] none none
        none none false none none)
      (Resolved.Query.oneTable innerPosition outer innerCondition [.literal (.integer 1)] ["1"]) none)
    (mainResolved : List (List (Resolved.Output × String × Option Affinity))) (mainProjections : List Resolved.Expr)
    (mainNames : List String) (mainCondition : Resolved.Expr)
    (mainColumnsOk : resolveAll (resolveResultColumn context.profile.dqsDml outerScope { later := [shape] })
      mainColumns = .ok mainResolved)
    (mainOutputs : mainResolved.flatten.map (·.1) = mainProjections.map Resolved.Output.scalar)
    (mainOutputNames : mainResolved.flatten.map (·.2.1) = mainNames)
    (mainFilterOk : FilterResolves context.profile.dqsDml outerScope
      ((resultAliases outerScope mainColumns).filterMap id) (some mainFilter) (some mainCondition) { later := [shape] })
    (mainNoFeed : (mainResolved.flatten.filterMap fun (output, _) => match output with
      | .scalar expression => some expression
      | .aggregate _ => none).any (fun expression =>
        expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false) :
    resolveStatement context state (.select mainColumns (some mainReference) [] (some mainFilter) [] [] none none
        [Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some innerReference) [] innerFilter [] [] none none
          none none false none none] none false none) =
      .ok (.query (Resolved.Query.oneTable position 0 (some mainCondition) mainProjections mainNames)
        [Resolved.Query.oneTable innerPosition outer innerCondition [.literal (.integer 1)] ["1"]], state) := by
  have result := resolveStatement_selectFrom_subquery context state mainReference innerReference mainColumns
    [.expression (.numeric "1") none "1"] mainFilter innerFilter position innerPosition outer table innerTable
    mainNamed mainSchema mainArguments mainFound innerNamed innerSchema innerArguments innerFound outerIs
    outerScope innerScope outerScopeIs innerScopeIs mainPlain rfl mainNoStar (by simp [starIssue])
    [[(.scalar (.literal (.integer 1)), "1", none)]] innerCondition
    (by subst outerScopeIs innerScopeIs; exact resolveColumns_one _ _ _)
    (by simpa [resultAliases] using innerFilterOk) (by simp [Resolved.Expr.any, Resolved.Expr.isFallibleCall])
    shape shapeIs mainResolved mainCondition mainColumnsOk mainFilterOk mainNoFeed
  rw [result, mainOutputs, mainOutputNames]
  rfl

/-- In a statement with one subquery that has no parent, the test {lit}`EXISTS` of subquery 0 is a condition that
resolves to {lit}`EXISTS` of subquery 0, in any scope and for any result-column aliases. It is the hypothesis
{lit}`mainFilterOk` of {name}`resolveStatement_selectFrom_existsTest` for the positive test. Proof sketch:
{name}`FilterResolves.of_term` with {name}`resolveOperand_exists` and {name}`SubqueryShapes.find_only`. -/
theorem FilterResolves.exists_only {dqs : Bool} {scope : Scope} {shape : SubqueryShape} (aliases : List Identifier)
    (parentless : shape.parent = none) :
    FilterResolves dqs scope aliases (some (.exists 0)) (some (.exists 0)) { later := [shape] } :=
  FilterResolves.of_term (result := (.exists 0, none)) (by simp [namesAlias])
    (resolveOperand_exists (SubqueryShapes.find_only parentless))

/-- In a statement with one subquery that has no parent, {lit}`NOT EXISTS` of subquery 0 is a condition that
resolves to {lit}`NOT EXISTS` of subquery 0, in any scope and for any result-column aliases. It is the hypothesis
{lit}`mainFilterOk` of {name}`resolveStatement_selectFrom_existsTest` for the negative test. Proof sketch:
{name}`FilterResolves.of_term`; {lit}`NOT` resolves its operand as a condition ({name}`resolveOperand_not`). -/
theorem FilterResolves.notExists_only {dqs : Bool} {scope : Scope} {shape : SubqueryShape}
    (aliases : List Identifier) (parentless : shape.parent = none) :
    FilterResolves dqs scope aliases (some (.not (.exists 0))) (some (.not (.exists 0))) { later := [shape] } :=
  FilterResolves.of_term (result := (.not (.exists 0), none)) (by simp [namesAlias])
    (by simp [resolveOperand_not, condition, resolveOperand_exists (SubqueryShapes.find_only parentless), Bind.bind,
      Except.bind])

end Belay.Sqlite.Model
