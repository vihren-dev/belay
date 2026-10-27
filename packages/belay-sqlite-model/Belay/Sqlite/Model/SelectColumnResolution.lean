import Belay.Sqlite.Model.SimpleStatementResolution
import Belay.Sqlite.Model.Resolution.ResultColumnArms
import Belay.Sqlite.Model.SelectOneResolution
import Belay.Sqlite.Model.SingleSourceNameLaws

set_option doc.verso true

/-! Resolution of a one-table {lit}`SELECT` that returns one named column (ADR 0017, S6). In the scope
of one physical table, a found identifier as the only result column resolves to its column position.
With a resolving filter, the whole statement resolves to the simple query of the table at its catalog
position, returning that column. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every dialect setting, subquery shapes, table position, table name, columns, rowid flag, alias
flag, identifier that names a column of the table, quote kind, alias and text: a found identifier as the
only result column resolves to its column position. Its output name and affinity are whatever the
resolver gives. The result is the same whether the source has an alias or not ({lit}`aliased`), because
the flag only tells a name trace whether the table was written with an alias. Proof sketch: unfold the
result-column resolver for an expression that is a name, then apply the single-source name law. -/
theorem resolveColumns_identifier_at (dqs : Bool) (shapes : SubqueryShapes) (position : Option Nat)
    (tableName : Identifier) (columns : List CatalogColumn) (rowid aliased : Bool) {id : Identifier}
    (quote : Syntax.QuoteKind) {idPosition : Nat} (found : columnPosition columns id = some idPosition)
    (alias : Option Identifier) (text : String) :
    ∃ (name : String) (affinity : Option Affinity),
      resolveAll (resolveResultColumn dqs (Scope.singleAt position tableName columns rowid aliased) shapes)
        [.expression (.identifier id quote) alias text] = .ok [[(.scalar (.column idPosition), name, affinity)]] := by
  simp [resolveAll, resolveAllFrom, resolveResultColumn_expression, resolveOperand_identifier_singleAt found, Bind.bind,
    Except.bind, Pure.pure, Except.pure, Except.mapError]

/-- For every resolution context and state, table reference that names a table without a schema, query or
arguments, catalog position, table, resolved condition, name of a returned column and result text: if the
catalog finds the table at the position, the table has the column, and the written filter resolves to the
condition in the scope of the table ({name}`FilterResolves`), then the one-table {lit}`SELECT` of the
column with that filter resolves to the simple query of the table at its catalog position, returning
that column, with no subquery and an unchanged state. The output name is whatever the resolver names it.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch:
{name}`resolveStatement_select_simple` with the table source, the one resolved column of
{name}`resolveColumns_identifier_at` and the filter. -/
theorem resolveStatement_select_column (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (filter : Option Syntax.Expr) (position : Nat) (table : CatalogTable)
    (condition : Option Resolved.Expr) (idName : Identifier) (text : String) {idPosition : Nat}
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : state.catalog.findTable reference.table = some (position, table))
    (idFound : columnPosition table.columns idName = some idPosition)
    (resolves : FilterResolves context.profile.dqsDml (tableScope state.catalog reference position table) []
      filter condition) :
    ∃ names, resolveStatement context state (.select [.expression (.identifier idName .none) none text]
        (some reference) [] filter [] [] none none [] none false none) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.first position] condition
        [.scalar (.column idPosition)] names) [], state) := by
  obtain ⟨name, affinity, columns⟩ := resolveColumns_identifier_at context.profile.dqsDml { later := [] } (some position)
    (reference.alias.getD ((state.catalog[position]?.map (·.name)).getD reference.table)) table.columns
    (!table.withoutRowid) reference.alias.isSome .none idFound none text
  have simple : (Syntax.Subquery.mk [.expression (.identifier idName .none) none text] (some reference) [] filter [] []
      none none none none false none none).Simple := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨[name], ?_⟩
  have result := resolveStatement_select_simple context state
    (Syntax.Subquery.mk [.expression (.identifier idName .none) none text] (some reference) [] filter [] [] none none
      none none false none none)
    simple rfl _ _ _ condition _ (resolveSources_table state.catalog reference position table namedSource current arguments found)
    (by simp [starIssue]) columns (by simpa [resultAliases] using resolves)
    (resolvePendingSources_table context.profile.dqsDml _ position)
    (by simp [Resolved.Expr.any, Resolved.Expr.isFallibleCall])
  simpa using result

end Belay.Sqlite.Model
