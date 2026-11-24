import Belay.Sqlite.Model.Queries.Evaluation.SimpleQueryAppend
import Belay.Sqlite.Model.Programs.StatementRunLaws.SelectCalmRule
import Belay.Sqlite.Model.Schema.Dispatch.TableSourceLaws
import Belay.Sqlite.Model.Schema.Ddl.TableByName
import Belay.Sqlite.Model.Programs.Scripts.QueryRule

set_option doc.verso true

/-! Data facts for one-table scans. Two calm scans can use different filters, result
names and table positions. Their modeled outputs agree if the second table adds cells
to each source row, the filters keep the same rows, and the projections read old cells. -/

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

/-- At every clock and index on a connection with the specified table, the modeled
output of a calm one-table scan is the normalized result on the table's scanned
rows and bound values. Proof sketch: apply the six checks of the simple query
to its output at clock value zero and empty counters. -/
theorem resolvedStepOutput_simpleTable (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) {position : Nat} {filter : Option Expr} {columns : List Resolved.Output}
    {names : List String} {table : Table} (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Query.simple [QuerySource.first position] filter columns names) []).Calm) :
    let query := Query.simple [QuerySource.first position] filter columns names
    resolvedStepOutput clock index connection parameters (.query query []) =
      .rows (normalForm (query.results (EvalContext.bound parameters) (sourceRows table))) := by
  dsimp only
  rw [resolvedStepOutput_query_at clock index connection parameters _ [] (value := 0)
    (by simp [statementClock, calm.readsClock]) (by simp [calm.counterReads])]
  simp [calm.counterReads, Query.simpleTable_checks parameters present calm, Query.outputOn,
    Belay.Sqlite.Model.Output.ofResults, List.eraseDups_cons, stableSort, insertStable]

/-- At a common clock and with the same bound values, two calm scans have equal
modeled outputs under the following conditions.

* Each connection has its table at the specified position. Their result names,
  positions and statement indexes can differ.
* The second table's source rows are the first table's source rows with the
  extra cells for each row appended. Every original row has at least the given width.
* The scans have the same result columns, all of which read only below the width.
* On every original row, the second filter on the extended row agrees with the
  first filter on the original row in the bound-parameter context.

Proof sketch: {name}`resolvedStepOutput_simpleTable` computes both normalized
outputs. Apply {name}`Query.simple_results_agree` to the source rows. -/
theorem resolvedStepOutput_simpleTable_agree (clock : Option Clock)
    (before after : Nat) (connection expanded : Connection)
    (parameters : List Value) (beforePosition afterPosition : Nat) (table extended : Table)
    (beforeFilter afterFilter : Option Expr) (columns : List Resolved.Output)
    (beforeNames afterNames : List String) (width : Nat) (extra : List Value → List Value)
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
    resolvedStepOutput clock before connection parameters
      (.query (Query.simple [QuerySource.first beforePosition] beforeFilter columns beforeNames) []) =
      resolvedStepOutput clock after expanded parameters
        (.query (Query.simple [QuerySource.first afterPosition] afterFilter columns afterNames) []) := by
  rw [resolvedStepOutput_simpleTable clock before connection parameters presentBefore calmBefore,
    resolvedStepOutput_simpleTable clock after expanded parameters presentAfter calmAfter,
    scans, Query.simple_results_agree (EvalContext.bound parameters) (EvalContext.plain_rowFree 0) (sourceRows table)
      extra [QuerySource.first beforePosition] [QuerySource.first afterPosition] beforeFilter afterFilter columns
      beforeNames afterNames width wide columnsBelow agree]

end Belay.Sqlite.Model
