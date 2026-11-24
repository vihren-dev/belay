import Belay.Sqlite.Model.Queries.Evaluation.SimpleQueryAppend
import Belay.Sqlite.Model.Programs.StatementRunLaws.SelectCalmRule
import Belay.Sqlite.Model.Schema.Dispatch.TableSourceLaws
import Belay.Sqlite.Model.Schema.Ddl.TableByName
import Belay.Sqlite.Model.Programs.Scripts.QueryRule

set_option doc.verso true

/-!
The outputs of a simple read of one table on two connections whose scans of the table differ by appended
cells (ADR 0017, S6). Both connections run the same statement. The statement resolves to the same
simple query on each connection, which reads the table that a name finds there (the positions can differ),
with a filter and scalar result columns that read only columns below a width. The scan of the table on the second connection is the scan on the
first with a computed list of cells appended to each row. Then the steps of the two connections give
the same output, whatever the clock and the statement indexes. This is the statement-level fact that
turns a dependency certificate of a read into the preservation of the read by a migration that adds
columns.
-/

namespace Belay.Sqlite.Model
open Resolved

/-- For every database, table position, table, filter, result columns, names and parameters,
suppose the table is at that position and the simple scan is calm. With clock value zero,
empty counter values and no subqueries, all six checks have known results:
* {name}`Query.described` holds.
* {name}`Query.runOn` gives the table scan and its run in the bound parameter context.
* The run has no window mismatch.
* The run has no overflow.
* The run has no fault.
* {name}`Query.possibleOn` gives only the normalized rows.

Proof sketch: {name}`Connection.SelectReady.of_calm` supplies readiness on the database.
{name}`Connection.queryContext_of_quiet` supplies the parameter context. Unfold the three
query data functions and apply the one-result law for an unordered scan. -/
theorem Resolved.Query.simpleTable_checks {db : Database} {position : Nat} {table : Table}
    {filter : Option Expr} {columns : List Resolved.Output} {names : List String}
    (parameters : List Value) (present : db.table position = some table)
    (calm : (Resolved.Statement.query (Query.simple [QuerySource.first position] filter columns names) []).Calm) :
    let query := Query.simple [QuerySource.first position] filter columns names
    let source : SourceRows := { rows := sourceRows table, width := table.shape.columns.length, fault := .none }
    let run := query.run (EvalContext.bound parameters) source.rows
    query.described 0 {} parameters db [] = true ∧ query.runOn 0 {} parameters db [] = some (source, run) ∧
      run.mismatch = false ∧ run.overflow = false ∧ run.fault = .none ∧
      query.possibleOn 0 {} parameters db [] = some [normalForm (query.results (EvalContext.bound parameters) source.rows)] := by
  let query := Query.simple [QuerySource.first position] filter columns names
  let source : SourceRows := { rows := sourceRows table, width := table.shape.columns.length, fault := .none }
  let connection : Connection := { state := { database := db } }
  have found : query.source (EvalContext.bound parameters) db = some source :=
    Query.source_first _ _ _ position table rfl present
  have ready := Connection.SelectReady.of_calm connection parameters calm rfl rfl rfl found (by simp [source]) rfl rfl
  change connection.SelectReady 0 parameters query [] source query at ready
  have emptyContext : statementContext 0 {} parameters db [] = EvalContext.bound parameters := by
    rw [statementContext_nil]
    rfl
  have ctx := Connection.queryContext_of_quiet connection parameters query calm.quiet
  have mismatch := ready.mismatch
  have overflow := ready.overflow
  have fault := ready.fault
  change (query.run (connection.queryContext parameters query []) source.rows).mismatch = false at mismatch
  change (query.run (connection.queryContext parameters query []) source.rows).overflow = false at overflow
  change (query.run (connection.queryContext parameters query []) source.rows).fault = .none at fault
  rw [ctx] at mismatch overflow fault
  have ran : query.runOn 0 {} parameters db [] = some (source, query.run (EvalContext.bound parameters) source.rows) := by
    simp [Query.runOn, emptyContext, found]
  refine ⟨?_, ran, mismatch, overflow, fault, ?_⟩
  · change query.described 0 {} parameters db [] = true
    simp [Query.described, ran, ready.plain, fault, source]
  · change query.possibleOn 0 {} parameters db [] = _
    simp [Query.possibleOn, emptyContext, found, ready.window,
      Query.possibleResults_unordered (query := query) _ rfl rfl rfl]
    rfl

/-- For every two connections, two statements and parameters that satisfy the premises below, the steps of
the statements on the two connections give the same output, at any clocks and statement indexes. The
premises are:

* The first statement resolves on the first connection to a simple query of the table at one position,
  and the second statement resolves on the second connection to a simple query of the table at one
  position, with the same result columns and possibly different filters and result names. Both
  queries are calm: they call no function that can fail and read no clock and no counter.
* The table of the second connection has a scan that is the scan of the table of the first connection with
  cells appended to each row. The cells can depend on the row.
* Every row of the first scan has at least {lit}`width` cells, and the result columns read only columns
  below the width ({name}`Output.readsBelow`).
* On each row of the first scan, the second filter on the row with its cells appended keeps the row exactly
  when the first filter keeps the row, in the context of the bound parameters.

In plain words, a query on the extended table that keeps the same rows as a query on the original table, and
returns columns of the original table, gives the same output. The two filters can be different
expressions, and the second can read the appended cells. For example, the query {lit}`SELECT id FROM t WHERE
lower(name) = lower(?1)` before a migration that stores {lit}`lower(name)` in a new column, and the query
{lit}`SELECT id FROM t WHERE stored = lower(?1)` after it, give the same output when the stored column
compares as {lit}`lower(name)` does. A query that selects every column does not resolve to the same columns, so
the premise about resolution fails for it. Proof sketch: {name}`Resolved.Query.simpleTable_checks` and {name}`runScriptStep_query_eq` for each
connection, then {name}`Query.simple_results_agree` with the row-free context of bound parameters. -/
theorem runScriptStep_simpleTable_output_agree (context : ResolveContext) (clock : Option Clock)
    (before after : Nat) (connection expanded : Connection) (beforeStatement afterStatement : Syntax.Statement)
    (parameters : List Value) (beforePosition afterPosition : Nat) (table extended : Table)
    (beforeFilter afterFilter : Option Expr) (columns : List Resolved.Output)
    (beforeNames afterNames : List String) (width : Nat) (extra : List Value → List Value)
    {beforeState afterState : ResolveState}
    (resolvedBefore : resolveStatement context connection.resolveState beforeStatement =
      .ok (.query (Query.simple [QuerySource.first beforePosition] beforeFilter columns beforeNames) [], beforeState))
    (resolvedAfter : resolveStatement context expanded.resolveState afterStatement =
      .ok (.query (Query.simple [QuerySource.first afterPosition] afterFilter columns afterNames) [], afterState))
    (presentBefore : connection.state.database.table beforePosition = some table)
    (presentAfter : expanded.state.database.table afterPosition = some extended)
    (calmBefore : (Resolved.Statement.query
      (Query.simple [QuerySource.first beforePosition] beforeFilter columns beforeNames) []).Calm)
    (calmAfter : (Resolved.Statement.query
      (Query.simple [QuerySource.first afterPosition] afterFilter columns afterNames) []).Calm)
    (scans : sourceRows extended = (sourceRows table).map fun row => row ++ extra row)
    (wide : ∀ row ∈ sourceRows table, width ≤ row.length)
    (columnsBelow : ∀ column ∈ columns, column.readsBelow width = true)
    (agree : ∀ row ∈ sourceRows table,
      (afterFilter.all fun condition => truthy (condition.eval (EvalContext.bound parameters) (row ++ extra row))) =
        (beforeFilter.all fun condition => truthy (condition.eval (EvalContext.bound parameters) row))) :
    (runScriptStep context clock before connection beforeStatement parameters).output =
      (runScriptStep context clock after expanded afterStatement parameters).output := by
  have rowsBefore : (runScriptStep context clock before connection beforeStatement parameters).output =
      .rows (normalForm ((Query.simple [QuerySource.first beforePosition] beforeFilter columns beforeNames).results
        (EvalContext.bound parameters) (sourceRows table))) := by
    simp [runScriptStep_query_eq resolvedBefore, statementClock, calmBefore.readsClock, calmBefore.counterReads,
      Query.simpleTable_checks parameters presentBefore calmBefore, List.eraseDups_cons, Resolved.stableSort,
      Resolved.insertStable, RunStep.output]
  have rowsAfter : (runScriptStep context clock after expanded afterStatement parameters).output =
      .rows (normalForm ((Query.simple [QuerySource.first afterPosition] afterFilter columns afterNames).results
        (EvalContext.bound parameters) (sourceRows extended))) := by
    simp [runScriptStep_query_eq resolvedAfter, statementClock, calmAfter.readsClock, calmAfter.counterReads,
      Query.simpleTable_checks parameters presentAfter calmAfter, List.eraseDups_cons, Resolved.stableSort,
      Resolved.insertStable, RunStep.output]
  rw [rowsBefore, rowsAfter,
    scans, Query.simple_results_agree (EvalContext.bound parameters) (EvalContext.plain_rowFree 0) (sourceRows table)
      extra [QuerySource.first beforePosition] [QuerySource.first afterPosition] beforeFilter afterFilter columns
      beforeNames afterNames width wide columnsBelow agree]

/-- For every two connections, statement, parameters and table name that satisfy the premises below, the
steps of the statement on the two connections give the same output, at any clocks and statement indexes.
The premises are those of {name}`runScriptStep_simpleTable_output_agree` for one statement with one filter
on both connections, which reads only columns below the width:
* The name finds a table in each connection ({name}`Database.tableNamed`), at positions that can differ,
  for example after the drop of an earlier table.
* The statement resolves on each connection to a simple query of the table at the position that the name
  finds there, with the same filter and result columns and possibly different result names.
* Both queries are calm, the scan of the second table is the scan of the first with cells appended to each
  row, and every scanned row of the first table has at least the width.

In plain words, appended cells that the query does not read cannot change its output. For example, a query
that selects the column {lit}`id` of rows filtered by {lit}`name = ?1` gives the same output after any column
is appended to the table, provided that the query still resolves to the same columns. Proof sketch:
{name}`runScriptStep_simpleTable_output_agree`, whose agreement premise holds because the filter reads below
the width ({name}`Query.filterKeeps_append`); the tables come from the lookups by name
({name}`Database.tableNamed_some`). -/
theorem runScriptStep_simpleTable_output_append (context : ResolveContext) (clock : Option Clock)
    (before after : Nat) (connection expanded : Connection) (statement : Syntax.Statement)
    (parameters : List Value) (name : Identifier) (beforePosition afterPosition : Nat) (table extended : Table)
    (filter : Option Expr) (columns : List Resolved.Output) (names other : List String) (width : Nat)
    (extra : List Value → List Value) {beforeState afterState : ResolveState}
    (foundBefore : connection.state.database.tableNamed name = some (beforePosition, table))
    (foundAfter : expanded.state.database.tableNamed name = some (afterPosition, extended))
    (resolvedBefore : resolveStatement context connection.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first beforePosition] filter columns names) [], beforeState))
    (resolvedAfter : resolveStatement context expanded.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first afterPosition] filter columns other) [], afterState))
    (calmBefore : (Resolved.Statement.query
      (Query.simple [QuerySource.first beforePosition] filter columns names) []).Calm)
    (calmAfter : (Resolved.Statement.query
      (Query.simple [QuerySource.first afterPosition] filter columns other) []).Calm)
    (scans : sourceRows extended = (sourceRows table).map fun row => row ++ extra row)
    (wide : ∀ row ∈ sourceRows table, width ≤ row.length)
    (filterBelow : ∀ condition ∈ filter, condition.readsBelow width = true)
    (columnsBelow : ∀ column ∈ columns, column.readsBelow width = true) :
    (runScriptStep context clock before connection statement parameters).output =
      (runScriptStep context clock after expanded statement parameters).output :=
  runScriptStep_simpleTable_output_agree context clock before after connection expanded statement statement
    parameters beforePosition afterPosition table extended filter filter columns names other width extra
    resolvedBefore resolvedAfter (Database.tableNamed_some foundBefore).2 (Database.tableNamed_some foundAfter).2
    calmBefore calmAfter scans wide columnsBelow fun row member =>
      Query.filterKeeps_append (EvalContext.bound parameters) (EvalContext.plain_rowFree 0) row (extra row) width
        (wide row member) filter filterBelow

end Belay.Sqlite.Model
