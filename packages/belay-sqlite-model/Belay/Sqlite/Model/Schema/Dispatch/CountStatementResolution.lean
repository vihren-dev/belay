import Belay.Sqlite.Model.Schema.Dispatch.SubquerySelectResolution
import Belay.Sqlite.Model.Schema.Dispatch.SelectOneResolution
import Belay.Sqlite.Model.Schema.Dispatch.PlainQueryRules
import Belay.Sqlite.Model.Queries.Select.CountStatementResolution

set_option doc.verso true

/-! The resolution of {lit}`SELECT 1 WHERE c(SELECT count(*) FROM t WHERE p)` (ADR 0017, S4), the query form
of a bound on the number of rows: for a table that the catalog has, the statement resolves to the simple
query without source and with the condition {lit}`c`, and the one subquery, the count query of the first
source of the table with the condition that {lit}`p` resolves to in the scope of the table. -/

namespace Belay.Sqlite.Model

/-- For every statement {lit}`SELECT 1 WHERE c` with one subquery {lit}`SELECT count(*) FROM t WHERE p` of a table that
the catalog of the state has at a position, without table-function arguments, where {lit}`p` resolves in the
scope of the table to a condition, {lit}`c` resolves to a condition that has no fallible call for every shape of a
count query ({name}`countShape`), resolution gives the simple query without source and with that condition, the
literal one named {lit}`"1"`, and the count query of the first source of the table with the condition of {lit}`p` as its
one subquery, and leaves the state as it is. The source reference has no indexed query.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch: {name}`resolveStatement_select_of_resolveSelect` and
{name}`resolveSelect_noFrom_one_subquery`; the subquery resolves by {name}`resolveQueryBody_count` in the scope of its table
({name}`resolveSources_table`, {name}`resolvePendingSources_table`), its shape is that of a count query
({name}`subqueryShape_count`), and the statement's query resolves by {name}`resolveQueryBody_simple` in the empty scope
with that shape. -/
theorem resolveStatement_selectOne_count (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (subFilter : Option Syntax.Expr) (mainFilter : Syntax.Expr)
    (position : Nat) (table : CatalogTable) (subCondition : Option Resolved.Expr) (mainCondition : Resolved.Expr)
    (name : String) (text : String) (count : normalizeIdentifier name = "count")
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : state.catalog.findTable reference.table = some (position, table))
    (subResolves : FilterResolves context.profile.dqsDml (tableScope state.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (mainResolves : ∀ lowest : Option Nat,
      FilterResolves context.profile.dqsDml [] [] (some mainFilter) (some mainCondition) { later := [countShape lowest] })
    (plain : mainCondition.any Resolved.Expr.isFallibleCall = false) :
    resolveStatement context state (.select [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none none
        [Syntax.Subquery.mk [.expression (.callStar name) none text] (some reference) [] subFilter [] [] none none none none
          false none none] none false none) =
      .ok (.query (Resolved.Query.selectOneWhere mainCondition)
        [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition text], state) := by
  have simple : ∀ source filter, (Syntax.Subquery.mk [.expression (.numeric "1") none "1"] source [] filter [] [] none none
      none none false none none).Simple := fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have noFeed : (([[(Resolved.Output.scalar (.literal (.integer 1)), "1", (none : Option Affinity))]] :
      List (List (Resolved.Output × String × Option Affinity))).flatten.filterMap fun (output, _) => match output with
      | .scalar expression => some expression
      | .aggregate _ => none).any (fun expression =>
        expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false := by
    simp [Resolved.Expr.any, Resolved.Expr.isFallibleCall]
  have subBody := resolveQueryBody_count context.profile.dqsDml (tableScope state.catalog reference position table) (some 0)
    [] [] _ (some reference) subFilter name none text count subCondition _ (by simpa [resultAliases] using subResolves)
    (resolvePendingSources_table _ _ position)
  obtain ⟨lowest, shapeIs⟩ := subqueryShape_count (tableScope state.catalog reference position table) { current := some 0 }
    (some reference) subFilter name none text
    (Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition text) rfl
  have mainBody := resolveQueryBody_simple context.profile.dqsDml [] none [countShape lowest] [] []
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
