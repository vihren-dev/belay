import Belay.Sqlite.Model.SimpleQueryAppend
import Belay.Sqlite.Model.SimpleTableRowsOutput
import Belay.Sqlite.Model.QueryStepOutput

set_option doc.verso true

/-!
The outputs of a simple read of one table on two connections whose scans of the table differ by appended
cells (ADR 0017, S6). Both connections run the same statement. The statement resolves to the same
simple query on each connection, which reads one table, with a filter and scalar result columns that
read only columns below a width. The scan of the table on the second connection is the scan on the
first with a computed list of cells appended to each row. Then the steps of the two connections give
the same output, whatever the clock and the statement indexes. This is the statement-level fact that
turns a dependency certificate of a read into the preservation of the read by a migration that adds
columns.
-/

namespace Belay.Sqlite.Model
open Resolved

/-- For every connection, statement, parameters, clock and index, if the statement resolves to a simple
query of the table at a position, with a calm filter and calm result columns, and the connection has
that table, then the output of its step is the rows of the query over the scan of the table, in normal
form. In plain words, such a read has the one output that the model gives for its rows, and it does not
depend on the clock or the index. Proof sketch: {name}`runScriptStep_output` gives the output of the
resolved statement, which {name}`resolvedStepOutput_simpleTable_rows` computes. -/
theorem runScriptStep_simpleTable_output (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (statement : Syntax.Statement) (parameters : List Value) (position : Nat)
    (table : Table) (filter : Option Expr) (columns : List Resolved.Output) (names : List String)
    {afterState : ResolveState}
    (resolved : resolveStatement context connection.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first position] filter columns names) [], afterState))
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Query.simple [QuerySource.first position] filter columns names) []).Calm) :
    (runScriptStep context clock index connection statement parameters).output =
      .rows (normalForm ((Query.simple [QuerySource.first position] filter columns names).results
        (EvalContext.bound parameters) (sourceRows table))) := by
  rw [runScriptStep_output, resolved]
  exact resolvedStepOutput_simpleTable_rows clock index position connection parameters table filter columns names
    present calm

/-- For every two connections, statement and parameters that satisfy the premises below, the steps of
the statement on the two connections give the same output, at any clocks and statement indexes. The
premises are:

* The statement resolves on each connection to a simple query of the table at one position, with the
  same filter and result columns, and with possibly different result names. Both queries are calm: they
  call no function that can fail and read no clock and no counter.
* The table of the second connection has a scan that is the scan of the table of the first connection with
  cells appended to each row. The cells can depend on the row.
* Every row of the first scan has at least {lit}`width` cells, and the filter and the result columns read
  only columns below the width ({name}`Output.readsBelow`).

In plain words, appended cells that the query does not read cannot change its output. For example, a query
that selects the column {lit}`id` of rows filtered by {lit}`name = ?1` gives the same output after any column
is appended to the table, provided that the query still resolves to the same columns. A query that selects
every column does not resolve to the same columns, so the premise about resolution fails for it. Proof
sketch: {name}`runScriptStep_simpleTable_output` for each connection, then
{name}`Query.simple_results_append` with the row-free context of bound parameters. -/
theorem runScriptStep_simpleTable_output_append (context : ResolveContext) (clock : Option Clock)
    (before after : Nat) (connection expanded : Connection) (statement : Syntax.Statement)
    (parameters : List Value) (position : Nat) (table extended : Table) (filter : Option Expr)
    (columns : List Resolved.Output) (names other : List String) (width : Nat) (extra : List Value → List Value)
    {afterState expandedState : ResolveState}
    (resolvedBefore : resolveStatement context connection.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first position] filter columns names) [], afterState))
    (resolvedAfter : resolveStatement context expanded.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first position] filter columns other) [], expandedState))
    (presentBefore : connection.state.database.table position = some table)
    (presentAfter : expanded.state.database.table position = some extended)
    (calm : (Resolved.Statement.query (Query.simple [QuerySource.first position] filter columns names) []).Calm)
    (scans : sourceRows extended = (sourceRows table).map fun row => row ++ extra row)
    (wide : ∀ row ∈ sourceRows table, width ≤ row.length)
    (filterBelow : ∀ condition ∈ filter, condition.readsBelow width = true)
    (columnsBelow : ∀ column ∈ columns, column.readsBelow width = true) :
    (runScriptStep context clock before connection statement parameters).output =
      (runScriptStep context clock after expanded statement parameters).output := by
  rw [runScriptStep_simpleTable_output context clock before connection statement parameters position table filter
      columns names resolvedBefore presentBefore calm,
    runScriptStep_simpleTable_output context clock after expanded statement parameters position extended filter
      columns other resolvedAfter presentAfter calm,
    scans, Query.simple_results_append (EvalContext.bound parameters) (EvalContext.plain_rowFree 0) (sourceRows table)
      extra _ filter columns names other width wide filterBelow columnsBelow]

end Belay.Sqlite.Model
