import Belay.Sqlite.Model.Schema.Dispatch.SimpleStatementResolution
import Belay.Sqlite.Model.Queries.Preparation.TableInfoResolution

set_option doc.verso true

/-! The resolution of the source {lit}`pragma_table_info('t')` (ADR 0017, S4): when the catalog has no table or view of the
name of the function, the source resolves to the one pragma source with the rows of {lit}`Catalog.tableInfoRows` for the
table {lit}`t`, and the scope of its columns and its two hidden cells. -/

namespace Belay.Sqlite.Model

/-- For every statement {lit}`SELECT 1 FROM pragma_table_info('t') WHERE p` (or without {lit}`WHERE`) whose reference
is as in {name}`resolveSources_tableInfo` and whose condition resolves in the scope of the pragma
({name}`tableInfoScope`) to a condition ({name}`FilterResolves`), resolution gives the simple query of the pragma
source with the rows of {name}`resolveSources_tableInfo`, the literal one named {lit}`"1"`, and that condition, with no
subquery, and leaves the state as it is. The source reference has no indexed query.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch: {name}`resolveStatement_select_simple` with the source of
{name}`resolveSources_tableInfo`, the pending source of {name}`resolvePendingSources_pragma` and the column of
{name}`resolveColumns_one`; the only column is not a star and calls no aggregate. -/
theorem resolveStatement_select_one_tableInfo (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (argument : List UInt8) (rows : List (List Value)) (filter : Option Syntax.Expr)
    (condition : Option Resolved.Expr) (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = some [.string argument])
    (isFunction : reference.table.isKeyword (bytes! "pragma_table_info") = true)
    (notTable : state.catalog.findTable reference.table = none)
    (notView : state.catalog.findView reference.table = none)
    (info : state.catalog.tableInfoRows ⟨argument⟩ = some rows)
    (resolves : FilterResolves context.profile.dqsDml (tableInfoScope reference argument rows) [] filter condition) :
    resolveStatement context state (.select [.expression (.numeric "1") none "1"] (some reference) [] filter [] [] none
        none [] none false none) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.pragma (pragmaSource reference argument tableInfoNames rows).1]
        condition [.scalar (.literal (.integer 1))] ["1"]) [], state) := by
  have columns := resolveColumns_one context.profile.dqsDml (tableInfoScope reference argument rows) { later := [] }
  have simple : (Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some reference) [] filter [] [] none none none
      none false none none).Simple :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have result := resolveStatement_select_simple context state
    (Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some reference) [] filter [] [] none none none none false none none)
    simple rfl _ _ _ condition _ (resolveSources_tableInfo state.catalog reference argument rows namedSource current arguments isFunction notTable notView info)
    (by simp [starIssue]) columns (by simpa [resultAliases] using resolves)
    (resolvePendingSources_pragma context.profile.dqsDml _ _)
    (by simp [Resolved.Expr.any, Resolved.Expr.isFallibleCall])
  simpa using result

end Belay.Sqlite.Model
