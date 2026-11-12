import Belay.Sqlite.Model.Schema.Dispatch.SelectOneResolution
import Belay.Sqlite.Model.Queries.Preparation.SelectColumnResolution

set_option doc.verso true

/-! Resolution of a one-table {lit}`SELECT` that returns one named column (ADR 0017, S6). In the scope
of one physical table, a found identifier as the only result column resolves to its column position.
With a resolving filter, the whole statement resolves to the simple query of the table at its catalog
position, returning that column. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every resolution context and state, table reference that names a table without a schema, query or
arguments, catalog position, table, written result columns, resolved columns and resolved condition: if the
catalog finds the table at the position, no result column calls an aggregate, no result column is a star with an issue ({name}`starIssue`), the
result columns resolve to {lit}`resolved` in the scope of the table, the written filter resolves to the
condition there with the aliases of the result columns ({name}`FilterResolves`), and no fallible call reads
an aggregate value, then the one-table {lit}`SELECT` of the columns with that filter resolves to the simple
query of the table at its catalog position, with the resolved outputs and their names in order, no
subquery and an unchanged state. The table reference names no schema: it is not a {lit}`before.t` source.
Proof sketch: {name}`resolveStatement_select_simple` with the table source of
{name}`resolveSources_table`. -/
theorem resolveStatement_select_table (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (filter : Option Syntax.Expr) (position : Nat) (table : CatalogTable)
    (condition : Option Resolved.Expr) (columns : List Syntax.ResultColumn)
    (resolved : List (List (Resolved.Output × String × Option Affinity)))
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : state.catalog.findTable reference.table = some (position, table))
    (noAggregate : (columns.all fun
      | .expression value _ _ => value.aggregateCalls.isEmpty
      | .star | .sourceStar _ => true) = true)
    (noStar : starIssue (tableScope state.catalog reference position table) columns = none)
    (columnsOk : resolveAll (resolveResultColumn context.profile.dqsDml (tableScope state.catalog reference position table)
      { later := [] }) columns = .ok resolved)
    (resolves : FilterResolves context.profile.dqsDml (tableScope state.catalog reference position table)
      ((resultAliases (tableScope state.catalog reference position table) columns).filterMap id) filter condition)
    (noFeed : (resolved.flatten.filterMap fun (output, _) => match output with
      | .scalar expression => some expression
      | .aggregate _ => none).any (fun expression =>
        expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false) :
    resolveStatement context state (.select columns (some reference) [] filter [] [] none none [] none false none) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.first position] condition
        (resolved.flatten.map (·.1)) (resolved.flatten.map (·.2.1))) [], state) :=
  resolveStatement_select_simple context state
    (Syntax.Subquery.mk columns (some reference) [] filter [] [] none none none none false none none)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, noAggregate⟩ rfl _ _ _ condition _
    (resolveSources_table state.catalog reference position table namedSource current arguments found)
    noStar columnsOk resolves (resolvePendingSources_table context.profile.dqsDml _ position) noFeed

/-- For every resolution context and state, table reference that names a table without a schema, query or
arguments, catalog position, table, resolved condition, name of a returned column and result text: if the
catalog finds the table at the position, the table has the column, and the written filter resolves to the
condition in the scope of the table ({name}`FilterResolves`), then the one-table {lit}`SELECT` of the
column with that filter resolves to the simple query of the table at its catalog position, returning
that column, with no subquery and an unchanged state. The output name is whatever the resolver names it.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch:
{name}`resolveStatement_select_table` with the one resolved column of
{name}`resolveColumns_identifier_at`. -/
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
  refine ⟨[name], ?_⟩
  simpa using resolveStatement_select_table context state reference filter position table condition _ _ namedSource
    current arguments found rfl (by simp [starIssue]) columns (by simpa [resultAliases] using resolves)
    (by simp [Resolved.Expr.any, Resolved.Expr.isFallibleCall])

end Belay.Sqlite.Model
