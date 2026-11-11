import Belay.Sqlite.Model.Queries.Select.SimpleStatementResolution
import Belay.Sqlite.Model.Schema.Dispatch.SimpleStatementResolution
import Belay.Sqlite.Model.Queries.Evaluation.StatementQuiet

set_option doc.verso true

/-! The resolution of {lit}`SELECT 1 FROM t WHERE p` (ADR 0017, S4), the query form of "some row
satisfies {lit}`p`": for a table that the catalog has, the statement resolves to the simple query
of the first source of that table, the integer literal one, and the condition that {lit}`p`
resolves to in the scope of the table. A statement without {lit}`WHERE` has no condition. -/

namespace Belay.Sqlite.Model

/-- For every statement {lit}`SELECT 1 FROM t WHERE p` (or without {lit}`WHERE`) of a table that the
catalog of the state has at a position, without table-function arguments, whose condition resolves
in the scope of the table to a condition ({name}`FilterResolves`), resolution gives the simple query
of the first source of the table, the literal one named {lit}`"1"`, and that condition, with no
subquery, and leaves the state as it is. The source reference has no indexed query.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch: {name}`resolveStatement_select_simple` with
the source of {name}`resolveSources_table`, the pending source of
{name}`resolvePendingSources_table` and the column of {name}`resolveColumns_one`; the only column
is not a star and calls no aggregate. -/
theorem resolveStatement_select_one_from (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (filter : Option Syntax.Expr) (position : Nat) (table : CatalogTable)
    (condition : Option Resolved.Expr) (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : state.catalog.findTable reference.table = some (position, table))
    (resolves : FilterResolves context.profile.dqsDml
      (tableScope state.catalog reference position table) [] filter condition) :
    resolveStatement context state (.select [.expression (.numeric "1") none "1"] (some reference) [] filter [] [] none
        none [] none false none) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.first position] condition
        [.scalar (.literal (.integer 1))] ["1"]) [], state) := by
  have columns := resolveColumns_one context.profile.dqsDml (tableScope state.catalog reference position table) { later := [] }
  have simple : (Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some reference) [] filter [] [] none none none
      none false none none).Simple :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have result := resolveStatement_select_simple context state
    (Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some reference) [] filter [] [] none none none none false none none)
    simple rfl _ _ _ condition _ (resolveSources_table state.catalog reference position table namedSource current arguments found)
    (by simp [starIssue]) columns (by simpa [resultAliases] using resolves)
    (resolvePendingSources_table context.profile.dqsDml _ position)
    (by simp [Resolved.Expr.any, Resolved.Expr.isFallibleCall])
  simpa using result

end Belay.Sqlite.Model
