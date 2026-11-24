import Belay.Sqlite.Model.Programs.StatementRunLaws.CertifiedQueryOutputs
import Belay.Sqlite.Model.Schema.Columns.DerivedColumnTable

set_option doc.verso true

/-! Reads of a table after a migration that adds a column, backfills it from an expression and registers
triggers (ADR 0017, S6). The laws combine the output agreement of two calm scans with the table that
the migration leaves ({name}`Belay.Sqlite.Model.Database.addDerivedColumn`) and the scan of that table. They
say when a scan has the same output before and after the migration, and what the rows of the
migrated table must satisfy for a moved read. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every connection with an original table, connection whose database is the migrated one, two
simple scans and bound parameters that satisfy the premises below, the scans give the same modeled output,
at any clocks and statement indexes. The premises are:

* The table is at a position inside the rows of the database, has wide aliased rows, key positions and
  columns inside the width, and no generated column. The appended column is not generated, and the
  expression reads only the old columns.
* Both scans use the same table position and result columns. They can use different filters and result names. Both queries are calm, and the result
  columns read only old columns.
* On each original row, with the stored value of the expression appended, the second filter keeps the row
  exactly when the first filter keeps the original row, in the context of the bound parameters.

In plain words, a read that returns old columns keeps its output when its filter is replaced by a filter
that keeps the same rows of the migrated table. The second filter can read the new column. The expression
need not be {lit}`lower` of a column, and the stored column's affinity enters only through the agreement
premise. Proof sketch: the migrated table at the position is {name}`Table.addDerivedColumn`
({name}`Database.table_addDerivedColumn`), its scan appends the stored value to each original row
({name}`sourceRows_addDerivedColumn`), and {name}`resolvedStepOutput_simpleTable_agree` compares the outputs. -/
theorem derivedColumn_lookup_outputs (clock : Option Clock) (before after : Nat)
    (connection migrated : Connection)
    (parameters : List Value) (position : Nat) (table : Table) (column : CatalogColumn) (derived : Resolved.Expr)
    (triggers : List (Identifier × CatalogTrigger)) (beforeFilter afterFilter : Option Expr)
    (columns : List Resolved.Output) (beforeNames afterNames : List String)
    (present : connection.state.database.table position = some table)
    (aligned : position < connection.state.database.rows.length)
    (reached : migrated.state.database =
      connection.state.database.addDerivedColumn position table column derived triggers)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (below : derived.readsBelow table.shape.columns.length = true)
    (keysInside : ∀ key ∈ table.shape.primaryKey, key < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) (newPlain : column.generated = none)
    (calmBefore : (Resolved.Statement.query
      (Query.simple [QuerySource.first position] beforeFilter columns beforeNames) []).Calm)
    (calmAfter : (Resolved.Statement.query
      (Query.simple [QuerySource.first position] afterFilter columns afterNames) []).Calm)
    (columnsBelow : ∀ output ∈ columns, output.readsBelow table.shape.columns.length = true)
    (agree : ∀ cells ∈ sourceRows table,
      (afterFilter.all fun condition => truthy (condition.eval (EvalContext.bound parameters)
        (cells ++ [Value.store column.affinity (derived.eval (EvalContext.plain 0) cells)]))) =
        (beforeFilter.all fun condition => truthy (condition.eval (EvalContext.bound parameters) cells))) :
    resolvedStepOutput clock before connection parameters
      (.query (Query.simple [QuerySource.first position] beforeFilter columns beforeNames) []) =
      resolvedStepOutput clock after migrated parameters
        (.query (Query.simple [QuerySource.first position] afterFilter columns afterNames) []) :=
  resolvedStepOutput_simpleTable_agree clock before after connection migrated
    parameters position position table (table.addDerivedColumn column derived) beforeFilter
    afterFilter columns beforeNames afterNames table.shape.columns.length
    (fun cells => [Value.store column.affinity (derived.eval (EvalContext.plain 0) cells)])
    present (by rw [reached]; exact Database.table_addDerivedColumn column derived triggers present aligned)
    calmBefore calmAfter (sourceRows_addDerivedColumn table column derived wide aliased below keysInside plain newPlain)
    (fun cells member => Nat.le_of_eq (sourceRows_width wide cells member).symm) columnsBelow agree

/-- For every connection with an original table, connection whose database is the migrated one, scan and
parameters that satisfy the premises of {name}`derivedColumn_lookup_outputs` for one filter that reads only
old columns on both connections, the two scans give the same modeled output, at any clocks and
statement indexes. In plain words, a read of old columns that does not read the new column keeps its output
across the migration: the added column, its backfill and the triggers cannot change it. Proof sketch:
{name}`resolvedStepOutput_simpleTable_agree` at one position with the scan of {name}`Table.addDerivedColumn`. -/
theorem derivedColumn_preserved_outputs (clock : Option Clock) (before after : Nat)
    (connection migrated : Connection) (parameters : List Value) (position : Nat)
    (table : Table) (column : CatalogColumn) (derived : Resolved.Expr) (triggers : List (Identifier × CatalogTrigger))
    (filter : Option Expr) (columns : List Resolved.Output) (names other : List String)
    (present : connection.state.database.table position = some table)
    (aligned : position < connection.state.database.rows.length)
    (reached : migrated.state.database =
      connection.state.database.addDerivedColumn position table column derived triggers)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (below : derived.readsBelow table.shape.columns.length = true)
    (keysInside : ∀ key ∈ table.shape.primaryKey, key < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) (newPlain : column.generated = none)
    (calm : (Resolved.Statement.query (Query.simple [QuerySource.first position] filter columns names) []).Calm)
    (filterBelow : ∀ condition ∈ filter, condition.readsBelow table.shape.columns.length = true)
    (columnsBelow : ∀ output ∈ columns, output.readsBelow table.shape.columns.length = true) :
    resolvedStepOutput clock before connection parameters
      (.query (Query.simple [QuerySource.first position] filter columns names) []) =
      resolvedStepOutput clock after migrated parameters
        (.query (Query.simple [QuerySource.first position] filter columns other) []) :=
  resolvedStepOutput_simpleTable_agree clock before after connection migrated
    parameters position position table (table.addDerivedColumn column derived) filter filter columns names other
    table.shape.columns.length
    (fun cells => [Value.store column.affinity (derived.eval (EvalContext.plain 0) cells)])
    present (by rw [reached]; exact Database.table_addDerivedColumn column derived triggers present aligned)
    calm calm (sourceRows_addDerivedColumn table column derived wide aliased below keysInside plain newPlain)
    (fun cells member => Nat.le_of_eq (sourceRows_width wide cells member).symm) columnsBelow
    fun row member =>
      Query.filterKeeps_append (EvalContext.bound parameters) (EvalContext.plain_rowFree 0) row _
        table.shape.columns.length (Nat.le_of_eq (sourceRows_width wide row member).symm) filter filterBelow

end Belay.Sqlite.Model
