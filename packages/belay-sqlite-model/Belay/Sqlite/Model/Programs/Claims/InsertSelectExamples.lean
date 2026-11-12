import Belay.Sqlite.Model.Programs.Scripts.ScriptRunSingleton
import Belay.Sqlite.Model.Programs.Clock.ScriptRunExamples
import Belay.Sqlite.Model.Schema.Writes.InsertSelectExamples

set_option doc.verso true

/-! Examples of the executions of INSERT from a query (ADR 0019, D4, amended 2026-10-25), checked by
{lit}`#guard` when the package builds. The statement has one execution for each order in which
SQLite may read its source table. The examples check these facts:

* A source table with a {lit}`UNIQUE` column can be read by its scan or by the index, so INSERT
  from it has two executions that assign other rowids to the rows. A source without an index has one.
* A source error after rows that all succeed ends the statement and keeps no row, also when
  SQLite collects the rows first. The two cases differ in {lit}`last_insert_rowid()`.
* A conflict of an earlier row ends the statement before a later source error.
* A statement that reads its target is a statement with its own run.
* With {lit}`LIMIT`, the scan stops before a row that the index reads first, so one execution succeeds
  and the other fails with the same statement.
* The copy of a source under the rowids of the source is in {lit}`InsertSelectTransferExamples`. -/

namespace Belay.Sqlite.Model.InsertSelectExamples

open Belay.Sqlite.Model Syntax

/-- A new connection with an empty database. -/
def start : Connection := { state := { database := {}, counters := Counters.newConnection } }

/-- The runs of all complete executions of the statements, from the empty database, where
statement {lit}`i` reads the values of item {lit}`i` of {lit}`values`. -/
def runs (script : List Syntax.Statement) (values : List (List Value) := []) : List ScriptRun :=
  runScriptAllFrom context none 0 start (bindValues script values)

/-- The output lists of all complete executions. -/
def allOutputs (script : List Syntax.Statement) (values : List (List Value) := []) : List (List Output) :=
  (runs script values).map (·.outputs)

/-- The rows of the table at the position, in scan order, after each complete execution. -/
def tables (position : Nat) (script : List Syntax.Statement) (values : List (List Value) := []) :
    List (Option (List (List Value))) :=
  (runs script values).map fun run => (run.connection.state.database.table position).map fun table =>
    table.scanRows.map (·.values)

-- With an index on x, the statement has two executions: the scan assigns the rowids 1 and 2 to 20 and
-- 10, as the model's own run does, and the index order assigns them to 10 and 20, as native 3.51.0 does
-- for this statement. Both end with the change count 2.
#guard tables 2 indexedCopy (twoRows 3) ==
  [some [[.integer 1, .integer 20], [.integer 2, .integer 10]],
    some [[.integer 1, .integer 10], [.integer 2, .integer 20]]]
#guard (allOutputs indexedCopy (twoRows 3)).map (·.getLast?) == [some (.done 2), some (.done 2)]

-- The first execution is the model's own run.
#guard (runs indexedCopy (twoRows 3)).head?.map (·.outputs) ==
  some (runScriptFrom context none 0 start (bindValues indexedCopy (twoRows 3))).outputs

-- Without an index there is one order, and so one execution.
#guard tables 1 plainCopy (twoRows 2) == [some [[.integer 1, .integer 20], [.integer 2, .integer 10]]]

-- The query fails after a row that was inserted into another table: the statement rolls back, so the
-- target has no row, and last_insert_rowid() is the rowid of the last row that the statement wrote.
#guard allOutputs (overflowScript "t" [createIdTarget]) (overflowValues 2) ==
  [[.done 0, .done 0, .done 1, .done 1, .error 1, .rows [[.integer 5]]]]

-- A query that reads the written table is collected before the first write, so the failure comes before
-- any write and last_insert_rowid() stays at the rowid of the last row of the source.
#guard allOutputs (overflowScript "s" []) (overflowValues 1) ==
  [[.done 0, .done 1, .done 1, .error 1, .rows [[.integer 2]]]]

-- A conflict of an earlier row ends the statement before the failure of a later source row: the
-- error is the constraint error 19, not the overflow.
#guard (allOutputs (plainSource ++ [createIdTarget, insertFive, insertParameter, insertParameter, insertAbs "t" "s"])
    (overflowValues 3)).map (·.getLast?) == [some (.error 19)]

-- INSERT of the rows of a table into the table does not grow without end: it doubles the rows once.
#guard (allOutputs (plainSource ++ [insertParameter, insertParameter, insertAbs "s" "s"])
    [[], [.integer 1], [.integer 2]]).map (·.getLast?) == [some (.done 2)]

-- A statement with a trigger is described for one order of its source only. A source with two orders
-- (a scan and an index) is not described: the statement ends the run as a statement that the model does
-- not run. With one order the trigger runs as for VALUES rows and the change count is the rows of the
-- statement.
#guard (allOutputs (triggeredCopy indexedSource) (twoRows 5)).map (·.getLast?.map Output.endsRun) == [some true]
#guard (allOutputs (triggeredCopy plainSource) (twoRows 4)).map (·.getLast?) == [some (.done 2)]

-- The scan reaches the row 5 and stops at the limit. The index reaches the smallest integer first, and
-- abs of it is an integer overflow, so that execution is an error and the target stays empty (native
-- 3.51.0 gives both results). Each execution has its own later query.
#guard (allOutputs limitedCopy (overflowValues 3)).map (·.drop 5) ==
  [[.done 1, .rows [[.integer 5]]], [.error 1, .rows []]]

end Belay.Sqlite.Model.InsertSelectExamples
