import Belay.Sqlite.Model.Programs.Clock.ScriptRunExamples
import Belay.Sqlite.Model.Schema.Writes.CounterExamples

set_option doc.verso true

/-! Examples of the counters of a connection after plain writes (ADR 0024, D2), each checked by
the kernel. The expected values are the values that native SQLite 3.51.0 gives for the same
statements (ADR 0024, "Examples"): an INSERT of two rows changes two and sets the last rowid; a
failed INSERT changes none and keeps the rowid of the last row stored before the failure; an
UPDATE or DELETE leaves the last rowid; a query, {lit}`BEGIN` and {lit}`ROLLBACK` leave all
three counters; a total that is unknown stays unknown. -/

namespace Belay.Sqlite.Model.CounterExamples

open Belay.Sqlite.Model Syntax Resolution.Examples ScriptRunExamples

/-- The counters after the statements, from the empty database on a connection with the supplied
counters: a new connection ({name}`Counters.newConnection`) by default. -/
def countersAfter (script : List Syntax.Statement) (start : Counters := Counters.newConnection) : Counters :=
  (runScriptFrom { profile := defaults, mode := .execution } none 0 { state := { database := {}, counters := start } }
    (bindValues script [])).connection.state.counters

/-- A statement that changes no counter leaves a new connection as it was. -/
example : countersAfter [createT, selectNames, .begin, .commit] = Counters.newConnection := by decide +kernel

/-- An INSERT of two rows changes two, adds two to the total, and sets the last rowid to 9. -/
example : countersAfter [createT, insertTwo] = { changes := some 2, totalChanges := some 2, lastInsertRowid := some 9 } := by
  decide +kernel

/-- A ROLLBACK keeps the counters of the INSERT that it rolls back. -/
example : countersAfter [createT, .begin, insertTwo, .rollback] =
    { changes := some 2, totalChanges := some 2, lastInsertRowid := some 9 } := by
  decide +kernel

/-- An {lit}`INSERT OR FAIL` that stops at its second row keeps the first: it changes one row, adds
one to the total, and sets the last rowid to the rowid 11 of the kept row. -/
example : countersAfter [createT, insertTwo,
      .insert (name! "t") none [[.numeric "11", .string "n".toUTF8.toList], [.numeric "5", .string "q".toUTF8.toList]] [] (some .fail)] =
    { changes := some 1, totalChanges := some 3, lastInsertRowid := some 11 } := by
  decide +kernel

/-- An {lit}`INSERT OR ABORT` that stops at its second row takes the first back: it changes none and
adds none to the total, but the last rowid keeps the rowid 11 that the statement stored. -/
example : countersAfter [createT, insertTwo,
      .insert (name! "t") none [[.numeric "11", .string "n".toUTF8.toList], [.numeric "5", .string "q".toUTF8.toList]] [] (some .abort)] =
    { changes := some 0, totalChanges := some 2, lastInsertRowid := some 11 } := by
  decide +kernel

/-- A connection with unknown counters learns {lit}`changes()` and the last rowid from an INSERT, and
keeps its total unknown. -/
example : countersAfter [createT, insertTwo] {} = { changes := some 2, lastInsertRowid := some 9 } := by
  decide +kernel

end Belay.Sqlite.Model.CounterExamples
