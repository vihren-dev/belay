import Belay.Sqlite.Model.Schema.Dispatch.SubquerySelectResolution
import Belay.Sqlite.Model.Queries.Select.AggregateSelectResolution

set_option doc.verso true

/-! The resolution of the whole-table aggregate query {lit}`SELECT agg(x) FROM t WHERE p` (ADR 0017, S4), such as
{lit}`SELECT sum(c) FROM t`: the body of the query, with its one result column an aggregate of one operand and its
{lit}`WHERE` condition, resolves to the whole-table aggregate query
({lit}`Resolved.Query.aggregateOf`, defined below) of its resolved sources, condition and aggregate. The lemmas
take the resolved sources, operand and condition as hypotheses, because the catalog is free. -/

namespace Belay.Sqlite.Model

/-- For every statement {lit}`SELECT agg(x) FROM t WHERE p` (or without {lit}`WHERE`) of a table that the catalog of the
state has at a position, without table-function arguments, whose aggregate {lit}`agg` is one of one operand that does not write
JSON ({name}`aggregateNamed`), whose operand resolves in the scope of the table and whose condition resolves
({name}`FilterResolves`), resolution gives the whole-table aggregate query of the first source of the table
({name}`Resolved.Query.aggregateOf`), with no subquery, and leaves the state as it is. The source reference has no indexed query.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch:
{name}`resolveStatement_select_of_resolveSelect` and {name}`resolveSelect_no_subqueries`; the body resolves by
{name}`resolveQueryBody_aggregate` in the scope of the table ({name}`resolveSources_table`,
{name}`resolvePendingSources_table`). -/
theorem resolveStatement_select_aggregate (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (filter : Option Syntax.Expr) (name : String) (operand : Syntax.Expr)
    (alias : Option Identifier) (text : String) (build : Resolved.Expr → Resolved.Aggregate)
    (named : aggregateNamed name = some build) (position : Nat) (table : CatalogTable) (resolved : Resolved.Expr)
    (affinity : Option Affinity) (condition : Option Resolved.Expr) (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : state.catalog.findTable reference.table = some (position, table))
    (operandOk : resolveOperand context.profile.dqsDml (tableScope state.catalog reference position table)
      { current := none, later := [] } true operand = .ok (resolved, affinity))
    (noJson : (build resolved).writesJson = false)
    (resolves : FilterResolves context.profile.dqsDml (tableScope state.catalog reference position table)
      ((resultAliases (tableScope state.catalog reference position table)
        [.expression (.call name [operand]) alias text]).filterMap id) filter condition { current := none, later := [] }) :
    resolveStatement context state (.select [.expression (.call name [operand]) alias text] (some reference) [] filter [] []
        none none [] none false none) =
      .ok (.query (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition
        ((build resolved).withCollation (operand.collationIn (tableScope state.catalog reference position table)))
        ((alias.map (·.text)).getD text)) [], state) := by
  refine resolveStatement_select_of_resolveSelect context state
    (Syntax.Subquery.mk [.expression (.call name [operand]) alias text] (some reference) [] filter [] [] none none none
      none false none none) [] rfl rfl _ ?_
  refine resolveSelect_no_subqueries context state.catalog _ _ none _ _ rfl rfl
    (resolveSources_table state.catalog reference position table namedSource current arguments found) (by simp [starIssue]) ?_
  have body := resolveQueryBody_aggregate context.profile.dqsDml (tableScope state.catalog reference position table)
    none [] [] _ (some reference) filter name operand alias text build named resolved affinity operandOk noJson condition
    _ (by simpa using resolves) (resolvePendingSources_table _ _ position)
  exact body

end Belay.Sqlite.Model
