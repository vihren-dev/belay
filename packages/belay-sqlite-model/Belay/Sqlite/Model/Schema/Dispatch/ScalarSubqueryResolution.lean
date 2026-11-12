import Belay.Sqlite.Model.Schema.Dispatch.SelectNoFromResolution
import Belay.Sqlite.Model.Schema.Dispatch.SubquerySelectResolution
import Belay.Sqlite.Model.Schema.Dispatch.SelectOneResolution
import Belay.Sqlite.Model.Schema.Dispatch.PlainQueryRules
import Belay.Sqlite.Model.Queries.Select.ScalarSubqueryResolution

set_option doc.verso true

/-! The resolution of {lit}`SELECT 1 WHERE c(SELECT e FROM t WHERE p)` (ADR 0017, S4), the statement whose
condition names a subquery with one expression column, such as {lit}`x IN (SELECT id FROM t WHERE p)` or a scalar
subquery: for a table that the catalog has, the statement resolves to the simple query without source and with the
condition {lit}`c`, and the one subquery, the simple query of the first source of the table with the condition that
{lit}`p` resolves to and the one column that {lit}`e` resolves to in the scope of the table. -/

namespace Belay.Sqlite.Model

/-- For every statement {lit}`SELECT 1 WHERE c` with one subquery {lit}`SELECT e FROM t WHERE p` of a table that the catalog of the
state has at a position, without table-function arguments, where {lit}`e` is no function call, has no aggregate call and resolves in
the scope of the table to an expression without a fallible call, {lit}`p` resolves in the scope of the table, and {lit}`c`
resolves to a condition without a fallible call for every lowest position of a one-column subquery with the collations of
{lit}`e` and its declared-type origin ({name}`scalarShape`), resolution gives the simple query without source,
with that condition and the literal one,
and the simple query of the first source of the table with the condition of {lit}`p` and the column of {lit}`e` as its one subquery,
and leaves the state as it is. The source reference has no indexed query.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch: {name}`resolveStatement_select_of_resolveSelect` and
{name}`resolveSelect_noFrom_one_subquery`; the subquery resolves by {name}`resolveQueryBody_simple` in the scope of its table
with the column of {name}`resolveColumns_scalar`, its shape is a one-column shape ({name}`subqueryShape_scalar`), and the
statement's query resolves by {name}`resolveQueryBody_simple` in the empty scope with that shape. -/
theorem resolveStatement_selectOne_scalar (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (value : Syntax.Expr) (text : String) (subFilter : Option Syntax.Expr)
    (mainFilter : Syntax.Expr) (position : Nat) (table : CatalogTable) (subCondition : Option Resolved.Expr)
    (mainCondition : Resolved.Expr) (expression : Resolved.Expr) (affinity : Option Affinity)
    (notCall : value.isCall = false) (noAggregate : value.aggregateCalls.isEmpty = true)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : state.catalog.findTable reference.table = some (position, table))
    (operand : resolveOperand context.profile.dqsDml (tableScope state.catalog reference position table)
      { current := some 0 } false value = .ok (expression, affinity))
    (valuePlain : expression.any Resolved.Expr.isFallibleCall = false)
    (subResolves : FilterResolves context.profile.dqsDml (tableScope state.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (mainResolves : ∀ lowest : Option Nat,
      FilterResolves context.profile.dqsDml [] [] (some mainFilter) (some mainCondition)
        { later := [scalarShape affinity value.explicitCollation (value.columnCollation
          (tableScope state.catalog reference position table)) lowest
          (value.originType (tableScope state.catalog reference position table) { current := some 0 })] })
    (plain : mainCondition.any Resolved.Expr.isFallibleCall = false) :
    resolveStatement context state (.select [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none none
        [Syntax.Subquery.mk [.expression value none text] (some reference) [] subFilter [] [] none none none none
          false none none] none false none) =
      .ok (.query (Resolved.Query.selectOneWhere mainCondition)
        [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition [.scalar expression]
          [(definedName (tableScope state.catalog reference position table) value).getD text]], state) := by
  have simple : ∀ source filter, (Syntax.Subquery.mk [.expression (.numeric "1") none "1"] source [] filter [] [] none none
      none none false none none).Simple := fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have noFeed : (([[(Resolved.Output.scalar (.literal (.integer 1)), "1", (none : Option Affinity))]] :
      List (List (Resolved.Output × String × Option Affinity))).flatten.filterMap fun (output, _) => match output with
      | .scalar expression => some expression
      | .aggregate _ => none).any (fun expression =>
        expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false := by
    simp [Resolved.Expr.any, Resolved.Expr.isFallibleCall]
  have subSimple : (Syntax.Subquery.mk [.expression value none text] (some reference) [] subFilter [] [] none none none none
      false none none).Simple := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simpa using noAggregate⟩
  have subBody := resolveQueryBody_simple context.profile.dqsDml (tableScope state.catalog reference position table)
    (some 0) [] [] _ (Syntax.Subquery.mk [.expression value none text] (some reference) [] subFilter [] [] none none
      none none false none none) subSimple _ subCondition _
    (resolveColumns_scalar _ _ _ value text expression affinity notCall operand)
    (by simpa [resultAliases] using subResolves) (resolvePendingSources_table _ _ position)
    (by simpa [Resolved.Expr.isFallibleCall] using Resolved.Expr.any_and_eq_false _ _ expression valuePlain)
  obtain ⟨lowest, shapeIs⟩ := subqueryShape_scalar (tableScope state.catalog reference position table)
    { current := some 0 } value none text (some reference) subFilter
    (Resolved.Query.simple [Resolved.QuerySource.first position] subCondition [.scalar expression]
      [(definedName (tableScope state.catalog reference position table) value).getD text]) affinity rfl
  have ordinary : value.flexibleNumeric (tableScope state.catalog reference position table)
      { current := some 0 } = false := by simp [tableScope, Syntax.Expr.flexibleNumeric_singleAt]
  rw [ordinary] at shapeIs
  have mainBody := resolveQueryBody_simple context.profile.dqsDml [] none
    [scalarShape affinity value.explicitCollation (value.columnCollation (tableScope state.catalog reference position table))
      lowest (value.originType (tableScope state.catalog reference position table) { current := some 0 })] [] []
    (Syntax.Subquery.mk [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none none none none false none none)
    (simple _ _) _ (some mainCondition) _ (resolveColumns_one _ _ _)
    (by simpa [resultAliases] using mainResolves lowest) (resolvePendingSources_nil _ _) noFeed
  refine resolveStatement_select_of_resolveSelect context state
    (Syntax.Subquery.mk [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none none none none false none none)
    _ rfl rfl _ ?_
  refine resolveSelect_noFrom_one_subquery context state.catalog _ _ rfl rfl rfl (by simp [starIssue]) rfl rfl rfl _ _
    (resolveSources_table state.catalog reference position table namedSource current arguments found) (by simp [starIssue]) _ _
    (by simpa [resultAliases] using subBody) _ shapeIs.symm _ _ (by simpa using mainBody) ?_
  simp [Resolved.Query.expressions, Resolved.Query.keptExpressions, Resolved.Query.simple, Resolved.Output.scalars,
    Resolved.Output.operands, plain, Resolved.Expr.any, Resolved.Expr.isFallibleCall]

end Belay.Sqlite.Model
