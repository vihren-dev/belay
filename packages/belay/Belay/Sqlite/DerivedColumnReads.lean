import Belay.Sqlite.DerivedColumnMigration

set_option doc.verso true

/-! The reads that a migration which adds a column, backfills it from an expression and registers triggers
moves or keeps (ADR 0017, S6). {lit}`Site.LookupMove` states what moves a read from the expression to the
stored column, and {lit}`Site.ReadPreserved` states what keeps a read as it is. For each, a theorem gives the
equal outputs of the steps before and after the migration. -/

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- The facts that move a read across the migration at a site, from the expression to the stored column. In
plain words, the read is a simple query of the table that returns old columns. Before the migration it has
one filter, and after it has another, which may read the new column. On the rows of the table the two
filters must keep the same rows, where a row after the migration is the old row with the stored value of
the expression appended. The fields are:

* The two queries resolve, on every resolution state with the catalog of the original and of the migrated
  database, to a simple query of the table at its position with these filters and the same result columns.
  The result names are arbitrary.
* Both queries are calm, and the result columns read only old columns.
* {lit}`agree`: when the rows of the table are wide, on every original row, in the context of the bound
  parameters, the second filter on the row with the stored value appended keeps the row exactly when the
  first filter keeps the original row.

The stored value is the value of {name}`Site.assigned` after the affinity of the new column. The
agreement does not require the two filters to be comparisons, and it does not mention {lit}`lower`. -/
structure Site.LookupMove {database : Database.Raw} {tableName : Identifier} {definition : Syntax.ColumnDefinition}
    {value : Syntax.Expr} (site : Site database tableName definition value)
    (triggers : List (Identifier × CatalogTrigger)) (original replacement : Syntax.Statement)
    (parameters : List Value) where
  /-- The filter of the original query. -/
  beforeFilter : Option Resolved.Expr
  /-- The filter of the replacement query. -/
  afterFilter : Option Resolved.Expr
  /-- The result columns of both queries. -/
  columns : List Resolved.Output
  /-- The result columns read only old columns. -/
  columnsBelow : ∀ output ∈ columns, output.readsBelow site.table.shape.columns.length = true
  /-- The original statement resolves to the original query. -/
  resolvesBefore : ∀ state : ResolveState, state.catalog = database.catalog →
    ∃ names after, resolveStatement runContext state original = .ok (.query
      (Resolved.Query.simple [Resolved.QuerySource.first site.position] beforeFilter columns names) [], after)
  /-- The replacement statement resolves to the replacement query on the migrated catalog. -/
  resolvesAfter : ∀ state : ResolveState, state.catalog = (site.reached triggers).catalog →
    ∃ names after, resolveStatement runContext state replacement = .ok (.query
      (Resolved.Query.simple [Resolved.QuerySource.first site.position] afterFilter columns names) [], after)
  /-- The original query is calm. -/
  calmBefore : ∀ names, (Resolved.Statement.query
    (Resolved.Query.simple [Resolved.QuerySource.first site.position] beforeFilter columns names) []).Calm
  /-- The replacement query is calm. -/
  calmAfter : ∀ names, (Resolved.Statement.query
    (Resolved.Query.simple [Resolved.QuerySource.first site.position] afterFilter columns names) []).Calm
  /-- When the rows of the table are wide, the filters keep the same rows of the migrated table. -/
  agree : site.table.RowsWide → ∀ cells ∈ Resolved.sourceRows site.table,
    (afterFilter.all fun condition => Resolved.truthy (condition.eval (Resolved.EvalContext.bound parameters)
      (cells ++ [Value.store site.column.affinity (site.assigned.eval (Resolved.EvalContext.plain 0) cells)]))) =
      (beforeFilter.all fun condition => Resolved.truthy (condition.eval (Resolved.EvalContext.bound parameters) cells))

/-- The facts that keep a read as it is across the migration at a site. In plain words, the read is a simple
query of the table that returns old columns, with a filter that reads only old columns. It resolves to the
same query, up to the result names, before and after the migration, and it is calm. For example, a lookup
that does not mention the new column resolves the same way, and a {lit}`SELECT *` does not. -/
structure Site.ReadPreserved {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr}
    (site : Site database tableName definition value) (triggers : List (Identifier × CatalogTrigger))
    (statement : Syntax.Statement) where
  /-- The filter of the query. -/
  filter : Option Resolved.Expr
  /-- The result columns of the query. -/
  columns : List Resolved.Output
  /-- The filter reads only old columns. -/
  filterBelow : ∀ condition ∈ filter, condition.readsBelow site.table.shape.columns.length = true
  /-- The result columns read only old columns. -/
  columnsBelow : ∀ output ∈ columns, output.readsBelow site.table.shape.columns.length = true
  /-- The statement resolves to the query on every resolution state with the catalog of the original database. -/
  resolvesBefore : ∀ state : ResolveState, state.catalog = database.catalog →
    ∃ names after, resolveStatement runContext state statement = .ok (.query
      (Resolved.Query.simple [Resolved.QuerySource.first site.position] filter columns names) [], after)
  /-- The statement resolves to the query on every resolution state with the catalog of the migrated database. -/
  resolvesAfter : ∀ state : ResolveState, state.catalog = (site.reached triggers).catalog →
    ∃ names after, resolveStatement runContext state statement = .ok (.query
      (Resolved.Query.simple [Resolved.QuerySource.first site.position] filter columns names) [], after)
  /-- The query is calm. -/
  calm : ∀ names, (Resolved.Statement.query
    (Resolved.Query.simple [Resolved.QuerySource.first site.position] filter columns names) []).Calm

/-- For every site, move of a read, connection on the site's database and connection on the migrated
database, with an aligned table of wide aliased rows, the steps of the original and replacement statements
have equal outputs, at any clocks and statement indexes. Proof sketch:
{name}`Model.derivedColumn_lookup_outputs` with the resolutions, calm facts and agreement of the move. -/
theorem Site.LookupMove.outputs {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} {site : Site database tableName definition value}
    {triggers : List (Identifier × CatalogTrigger)} {original replacement : Syntax.Statement}
    {parameters : List Value} (lookup : site.LookupMove triggers original replacement parameters)
    (clock : Option Clock) (before after : Nat) {connection migrated : Connection}
    (same : connection.state.database = database) (aligned : site.position < database.rows.length)
    (reached : migrated.state.database = site.reached triggers)
    (wide : site.table.RowsWide) (aliased : site.table.RowsAliased) :
    (runScriptStep runContext clock before connection original parameters).output =
      (runScriptStep runContext clock after migrated replacement parameters).output := by
  obtain ⟨names, beforeState, resolvedBefore⟩ := lookup.resolvesBefore connection.resolveState
    (by simp [Connection.resolveState, same])
  obtain ⟨afterNames, afterState, resolvedAfter⟩ := lookup.resolvesAfter migrated.resolveState
    (by simp [Connection.resolveState, reached])
  refine derivedColumn_lookup_outputs runContext clock before after connection migrated original replacement
    parameters site.position site.table site.column site.assigned triggers lookup.beforeFilter lookup.afterFilter
    lookup.columns names afterNames (by rw [same]; exact site.present) (by rw [same]; exact aligned)
    (by rw [reached, same]; rfl) wide aliased (assignedExpression_readsBelow site.below) site.keysInside site.plain
    (by simp [Site.column, definedColumn]) resolvedBefore resolvedAfter (lookup.calmBefore names)
    (lookup.calmAfter afterNames) lookup.columnsBelow (lookup.agree wide)

/-- For the premises of {name}`Site.LookupMove.outputs`, the original statement's step on the first
connection has the rows of some result as its output, and the replacement statement's step on the migrated
connection has the same rows. Plain words: a moved read returns rows, and the same rows before and after.
Proof sketch: the output of a calm read of one table is the normal form of the query result
({name}`Model.runScriptStep_simpleTable_output`), and {name}`Site.LookupMove.outputs` equates the two. -/
theorem Site.LookupMove.rows {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} {site : Site database tableName definition value}
    {triggers : List (Identifier × CatalogTrigger)} {original replacement : Syntax.Statement}
    {parameters : List Value} (lookup : site.LookupMove triggers original replacement parameters)
    (clock : Option Clock) (before after : Nat) {connection migrated : Connection}
    (same : connection.state.database = database) (aligned : site.position < database.rows.length)
    (reached : migrated.state.database = site.reached triggers)
    (wide : site.table.RowsWide) (aliased : site.table.RowsAliased) :
    ∃ rows, (runScriptStep runContext clock before connection original parameters).output = .rows rows ∧
      (runScriptStep runContext clock after migrated replacement parameters).output = .rows rows := by
  obtain ⟨names, beforeState, resolvedBefore⟩ := lookup.resolvesBefore connection.resolveState
    (by simp [Connection.resolveState, same])
  refine ⟨_, runScriptStep_simpleTable_output runContext clock before connection original parameters site.position
    site.table lookup.beforeFilter lookup.columns names resolvedBefore (by rw [same]; exact site.present)
    (lookup.calmBefore names), ?_⟩
  rw [← lookup.outputs clock before after same aligned reached wide aliased]
  exact runScriptStep_simpleTable_output runContext clock before connection original parameters site.position
    site.table lookup.beforeFilter lookup.columns names resolvedBefore (by rw [same]; exact site.present)
    (lookup.calmBefore names)

/-- For every site, read kept by {name}`Site.ReadPreserved`, connection on the site's database and connection
on the migrated database, with an aligned table of wide aliased rows, the steps of the statement on the two
connections have equal outputs, at any clocks and statement indexes. Proof sketch:
{name}`Model.derivedColumn_preserved_outputs` with the resolutions and calm facts of the read. -/
theorem Site.ReadPreserved.outputs {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} {site : Site database tableName definition value}
    {triggers : List (Identifier × CatalogTrigger)} {statement : Syntax.Statement}
    (read : site.ReadPreserved triggers statement) (parameters : List Value)
    (clock : Option Clock) (before after : Nat) {connection migrated : Connection}
    (same : connection.state.database = database) (aligned : site.position < database.rows.length)
    (reached : migrated.state.database = site.reached triggers)
    (wide : site.table.RowsWide) (aliased : site.table.RowsAliased) :
    (runScriptStep runContext clock before connection statement parameters).output =
      (runScriptStep runContext clock after migrated statement parameters).output := by
  obtain ⟨names, beforeState, resolvedBefore⟩ := read.resolvesBefore connection.resolveState
    (by simp [Connection.resolveState, same])
  obtain ⟨afterNames, afterState, resolvedAfter⟩ := read.resolvesAfter migrated.resolveState
    (by simp [Connection.resolveState, reached])
  exact derivedColumn_preserved_outputs runContext clock before after connection migrated statement parameters
    site.position site.table site.column site.assigned triggers read.filter read.columns names afterNames
    (by rw [same]; exact site.present) (by rw [same]; exact aligned) (by rw [reached, same]; rfl) wide aliased
    (assignedExpression_readsBelow site.below) site.keysInside site.plain (by simp [Site.column, definedColumn])
    resolvedBefore resolvedAfter (read.calm names) read.filterBelow read.columnsBelow

end Belay.Sqlite.DerivedColumnMigration
