import Belay.Sqlite.Model.CertifiedQueryOutputs
import Belay.Sqlite.Model.DerivedColumnTable

set_option doc.verso true

/-! Reads of a table after a migration that adds a column, backfills it from an expression and registers
triggers (ADR 0017, S6). The laws combine the certified-read law of two connections with the table that
the migration leaves ({name}`Belay.Sqlite.Model.Database.addDerivedColumn`) and the scan of that table. They
say when the step of a read has the same output before and after the migration, and what the rows of the
migrated table must satisfy for a moved read. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every connection with an original table, connection whose database is the migrated one, two
statements and parameters that satisfy the premises below, the steps of the statements give the same output,
at any clocks and statement indexes. The premises are:

* The table is at a position inside the rows of the database, has wide aliased rows, key positions and
  columns inside the width, and no generated column. The appended column is not generated, and the
  expression reads only the old columns.
* The first statement resolves on the original connection to a simple query of the table with a filter and
  result columns, and the second statement resolves on the migrated connection to a simple query of the same
  position with possibly another filter and the same result columns. Both queries are calm, and the result
  columns read only old columns.
* On each original row, with the stored value of the expression appended, the second filter keeps the row
  exactly when the first filter keeps the original row, in the context of the bound parameters.

In plain words, a read that returns old columns keeps its output when its filter is replaced by a filter
that keeps the same rows of the migrated table. The second filter can read the new column. The expression
need not be {lit}`lower` of a column, and the stored column's affinity enters only through the agreement
premise. Proof sketch: the migrated table at the position is {name}`Table.addDerivedColumn`
({name}`Database.table_addDerivedColumn`), its scan appends the stored value to each original row
({name}`sourceRows_addDerivedColumn`), and {name}`runScriptStep_simpleTable_output_agree` compares the outputs. -/
theorem derivedColumn_lookup_outputs (context : ResolveContext) (clock : Option Clock) (before after : Nat)
    (connection migrated : Connection) (beforeStatement afterStatement : Syntax.Statement)
    (parameters : List Value) (position : Nat) (table : Table) (column : CatalogColumn) (derived : Resolved.Expr)
    (triggers : List (Identifier × CatalogTrigger)) (beforeFilter afterFilter : Option Expr)
    (columns : List Resolved.Output) (beforeNames afterNames : List String) {beforeState afterState : ResolveState}
    (present : connection.state.database.table position = some table)
    (aligned : position < connection.state.database.rows.length)
    (reached : migrated.state.database =
      connection.state.database.addDerivedColumn position table column derived triggers)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (below : derived.readsBelow table.shape.columns.length = true)
    (keysInside : ∀ key ∈ table.shape.primaryKey, key < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) (newPlain : column.generated = none)
    (resolvedBefore : resolveStatement context connection.resolveState beforeStatement =
      .ok (.query (Query.simple [QuerySource.first position] beforeFilter columns beforeNames) [], beforeState))
    (resolvedAfter : resolveStatement context migrated.resolveState afterStatement =
      .ok (.query (Query.simple [QuerySource.first position] afterFilter columns afterNames) [], afterState))
    (calmBefore : (Resolved.Statement.query
      (Query.simple [QuerySource.first position] beforeFilter columns beforeNames) []).Calm)
    (calmAfter : (Resolved.Statement.query
      (Query.simple [QuerySource.first position] afterFilter columns afterNames) []).Calm)
    (columnsBelow : ∀ output ∈ columns, output.readsBelow table.shape.columns.length = true)
    (agree : ∀ cells ∈ sourceRows table,
      (afterFilter.all fun condition => truthy (condition.eval (EvalContext.bound parameters)
        (cells ++ [Value.store column.affinity (derived.eval (EvalContext.plain 0) cells)]))) =
        (beforeFilter.all fun condition => truthy (condition.eval (EvalContext.bound parameters) cells))) :
    (runScriptStep context clock before connection beforeStatement parameters).output =
      (runScriptStep context clock after migrated afterStatement parameters).output :=
  runScriptStep_simpleTable_output_agree context clock before after connection migrated beforeStatement
    afterStatement parameters position position table (table.addDerivedColumn column derived) beforeFilter
    afterFilter columns beforeNames afterNames table.shape.columns.length
    (fun cells => [Value.store column.affinity (derived.eval (EvalContext.plain 0) cells)]) resolvedBefore
    resolvedAfter present (by rw [reached]; exact Database.table_addDerivedColumn column derived triggers present aligned)
    calmBefore calmAfter (sourceRows_addDerivedColumn table column derived wide aliased below keysInside plain newPlain)
    (fun cells member => Nat.le_of_eq (sourceRows_width wide cells member).symm) columnsBelow agree

/-- For every connection with an original table, connection whose database is the migrated one, statement and
parameters that satisfy the premises of {name}`derivedColumn_lookup_outputs` for one filter that reads only
old columns on both connections, the steps of the statement give the same output, at any clocks and
statement indexes. In plain words, a read of old columns that does not read the new column keeps its output
across the migration: the added column, its backfill and the triggers cannot change it. Proof sketch:
{name}`runScriptStep_simpleTable_output_append` with the scan of {name}`Table.addDerivedColumn`. -/
theorem derivedColumn_preserved_outputs (context : ResolveContext) (clock : Option Clock) (before after : Nat)
    (connection migrated : Connection) (statement : Syntax.Statement) (parameters : List Value) (position : Nat)
    (table : Table) (column : CatalogColumn) (derived : Resolved.Expr) (triggers : List (Identifier × CatalogTrigger))
    (filter : Option Expr) (columns : List Resolved.Output) (names other : List String)
    {beforeState afterState : ResolveState}
    (present : connection.state.database.table position = some table)
    (aligned : position < connection.state.database.rows.length)
    (reached : migrated.state.database =
      connection.state.database.addDerivedColumn position table column derived triggers)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (below : derived.readsBelow table.shape.columns.length = true)
    (keysInside : ∀ key ∈ table.shape.primaryKey, key < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) (newPlain : column.generated = none)
    (resolvedBefore : resolveStatement context connection.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first position] filter columns names) [], beforeState))
    (resolvedAfter : resolveStatement context migrated.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first position] filter columns other) [], afterState))
    (calm : (Resolved.Statement.query (Query.simple [QuerySource.first position] filter columns names) []).Calm)
    (filterBelow : ∀ condition ∈ filter, condition.readsBelow table.shape.columns.length = true)
    (columnsBelow : ∀ output ∈ columns, output.readsBelow table.shape.columns.length = true) :
    (runScriptStep context clock before connection statement parameters).output =
      (runScriptStep context clock after migrated statement parameters).output :=
  runScriptStep_simpleTable_output_append context clock before after connection migrated statement parameters
    position table (table.addDerivedColumn column derived) filter columns names other table.shape.columns.length
    (fun cells => [Value.store column.affinity (derived.eval (EvalContext.plain 0) cells)]) resolvedBefore
    resolvedAfter present (by rw [reached]; exact Database.table_addDerivedColumn column derived triggers present aligned)
    calm (sourceRows_addDerivedColumn table column derived wide aliased below keysInside plain newPlain)
    (fun cells member => Nat.le_of_eq (sourceRows_width wide cells member).symm) filterBelow columnsBelow

end Belay.Sqlite.Model
