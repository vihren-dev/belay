import Belay.Sqlite.Schema.Columns.DerivedColumnMigration

set_option doc.verso true

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- The facts that move a read across the migration at a site, from the expression to the stored column. In
plain words, the read gives the output of a simple scan that returns old columns. Before the migration the scan has
one filter, and after it has another, which may read the new column. On the rows of the table the two
filters must keep the same rows, where a row after the migration is the old row with the stored value of
the expression appended. The fields are:

* On connections with the original and migrated catalogs, the two actual outputs match a simple scan of the table at its position with these filters and the same result columns.
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
  /-- On this catalog the actual statement has the output of the comparison scan. -/
  outputBefore : ∀ connection : Connection, connection.resolveState.catalog = database.catalog →
    ∃ names, ∀ clock index, (runScriptStep runContext clock index connection original parameters).output =
      resolvedStepOutput clock index connection parameters (.query
        (Resolved.Query.simple [Resolved.QuerySource.first site.position] beforeFilter columns names) [])
  /-- On this catalog the actual statement has the output of the comparison scan. -/
  outputAfter : ∀ connection : Connection, connection.resolveState.catalog = (site.reached triggers).catalog →
    ∃ names, ∀ clock index, (runScriptStep runContext clock index connection replacement parameters).output =
      resolvedStepOutput clock index connection parameters (.query
        (Resolved.Query.simple [Resolved.QuerySource.first site.position] afterFilter columns names) [])
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

/-- The facts that keep a read as it is across the migration at a site. The actual statement matches a calm
simple scan that returns and filters only old columns. This holds at every clock, index and list of bound
values, before and after the migration. The result names can differ. For example, a lookup
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
  /-- On this catalog the actual statement has the output of the comparison scan. -/
  outputBefore : ∀ connection : Connection, connection.resolveState.catalog = database.catalog →
    ∃ names, ∀ clock index parameters, (runScriptStep runContext clock index connection statement parameters).output =
      resolvedStepOutput clock index connection parameters (.query
        (Resolved.Query.simple [Resolved.QuerySource.first site.position] filter columns names) [])
  /-- On this catalog the actual statement has the output of the comparison scan. -/
  outputAfter : ∀ connection : Connection, connection.resolveState.catalog = (site.reached triggers).catalog →
    ∃ names, ∀ clock index parameters, (runScriptStep runContext clock index connection statement parameters).output =
      resolvedStepOutput clock index connection parameters (.query
        (Resolved.Query.simple [Resolved.QuerySource.first site.position] filter columns names) [])
  /-- The query is calm. -/
  calm : ∀ names, (Resolved.Statement.query
    (Resolved.Query.simple [Resolved.QuerySource.first site.position] filter columns names) []).Calm

end Belay.Sqlite.DerivedColumnMigration
