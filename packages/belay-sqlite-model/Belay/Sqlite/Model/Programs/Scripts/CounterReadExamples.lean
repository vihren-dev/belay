import Belay.Sqlite.Model.Programs.StatementRunLaws.CounterRowExamples
import Belay.Sqlite.Model.Queries.Preparation.CounterReadExamples

set_option doc.verso true

/-! Examples of the reads of the connection counters (ADR 0024, D2), each checked by the kernel.
The values are the values that native SQLite 3.51.0 gives for the same statements. A read gives the
value from before the statement. A read of a counter that the connection does not know ends the
run with the reason of {name}`Belay.Sqlite.Model.counterUnknownReason`, and such a statement is not supported. A
counter that no statement reads does not stop a run. The forms that the model does not describe are
restrictions: a read in a trigger program, a {lit}`CHECK` or a {lit}`DEFAULT`, {lit}`last_insert_rowid()`
in an INSERT, and {lit}`total_changes()` in a write that runs trigger programs. -/

namespace Belay.Sqlite.Model.CounterReadExamples

open Belay.Sqlite.Model Syntax Resolution.Examples ScriptRunExamples CounterExamples

/-- The outputs of the statements from the empty database on a connection with the counters. -/
def outputsFrom (counters : Counters) (script : List Syntax.Statement) : List Output :=
  (runScriptFrom { profile := defaults, mode := .execution } none 0 { state := { database := {}, counters } }
    (bindValues script [])).outputs

/-- {lit}`SELECT function()`, for the name of a counter function. -/
def readOf (function : String) : Syntax.Statement := selectOf (.call function [])

/-- Whether the support check ({name}`supportedSqlFrom`) holds for the statements from the empty
database on a connection with the counters. -/
def supportedFrom (counters : Counters) (script : List Syntax.Statement) : Bool :=
  supportedSqlFrom 0 (bindValues (statements (migration [] script)) []) { database := {}, counters }

/-- On a new connection, each counter after an INSERT of two rows (rowids 5 and 9) is a row. -/
example : outputsFrom Counters.newConnection
    [createT, insertTwo, readOf "changes", readOf "total_changes", readOf "last_insert_rowid"] =
    [.done 0, .done 2, .rows [[.integer 2]], .rows [[.integer 2]], .rows [[.integer 9]]] := by decide +kernel

/-- Before any write, a new connection reads 0 from each counter. -/
example : outputsFrom Counters.newConnection [readOf "changes", readOf "total_changes", readOf "last_insert_rowid"] =
    [.rows [[.integer 0]], .rows [[.integer 0]], .rows [[.integer 0]]] := by decide +kernel

/-- An INSERT reads {lit}`changes()` from before the statement: the new row has the id 2, the changes
of the earlier INSERT, and not 1; after it {lit}`changes()` is 1. -/
example : outputsFrom Counters.newConnection
    [createT, insertTwo, insertReadingChanges, selectIdOfX, readOf "changes"] =
    [.done 0, .done 2, .done 1, .rows [[.integer 2]], .rows [[.integer 1]]] := by decide +kernel

/-- A failed INSERT sets {lit}`changes()` to 0, and the next read sees 0. -/
example : outputsFrom Counters.newConnection [createT, insertTwo, insertFailing, readOf "changes"] =
    [.done 0, .done 2, .error 19, .rows [[.integer 0]]] := by decide +kernel

/-- With unknown counters, a statement that reads one ends the run with the reason that names it. -/
example : outputsFrom {} [readOf "changes", selectNames] = [.unmodeled (counterUnknownReason .changes)] := by
  decide +kernel

/-- Each of the three counters has its own reason. -/
example : outputsFrom {} [readOf "total_changes"] = [.unmodeled (counterUnknownReason .totalChanges)] := by
  decide +kernel
example : outputsFrom {} [readOf "last_insert_rowid"] = [.unmodeled (counterUnknownReason .lastInsertRowid)] := by
  decide +kernel

/-- A statement that does not read a counter runs with unknown counters, and a write that follows
makes {lit}`changes()` and {lit}`last_insert_rowid()` known, and not {lit}`total_changes()`. -/
example : outputsFrom {} [createT, insertTwo, readOf "changes", readOf "last_insert_rowid"] =
    [.done 0, .done 2, .rows [[.integer 2]], .rows [[.integer 9]]] := by decide +kernel
example : outputsFrom {} [createT, insertTwo, readOf "total_changes"] =
    [.done 0, .done 2, .unmodeled (counterUnknownReason .totalChanges)] := by decide +kernel

/-- A counter that no statement reads does not stop the run: only the unknown one that a statement
reads does. -/
example : outputsFrom { changes := some 3 } [readOf "changes", readOf "last_insert_rowid"] =
    [.rows [[.integer 3]], .unmodeled (counterUnknownReason .lastInsertRowid)] := by decide +kernel

/-- A statement with an unknown read is not supported, and one without is. -/
example : supportedFrom {} [readOf "changes"] = false := by decide +kernel
example : supportedFrom {} [createT, selectNames] = true := by decide +kernel
example : supportedFrom Counters.newConnection [readOf "changes", readOf "last_insert_rowid"] = true := by
  decide +kernel

end Belay.Sqlite.Model.CounterReadExamples
