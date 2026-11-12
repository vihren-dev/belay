import Belay.Sqlite.Model.Programs.Scripts.CounterRowExamples

set_option doc.verso true

/-! Examples of the counters of a connection after writes that run row by row (ADR 0024, D2),
each checked by the kernel: the rows of trigger programs and foreign-key actions count for
{lit}`total_changes()` and not for {lit}`changes()`, a nested insert does not set
{lit}`last_insert_rowid()`, a nested write that completed counts also when the statement fails
later, REPLACE does not count the row that it deletes, and DROP TABLE counts the rows of the table
and the rows of the actions. The expected values are the values that native SQLite 3.51.0 gives
for the same statements. -/

namespace Belay.Sqlite.Model.CounterRowExamples

open Belay.Sqlite.Model Syntax Resolution.Examples TriggerRunExamples

/-- A trigger program that inserts a row into {lit}`log` changes one row of {lit}`changes()` (the
row of the statement), adds both rows to the total, and leaves the last rowid at the rowid 1 of the
row in {lit}`t`, not the rowid 4 of the row in {lit}`log`. -/
example : countersUnder defaults (tables ++ [afterInsert [logged (.numeric "1")], logThree, insertSeven]) =
    { changes := some 1, totalChanges := some 5, lastInsertRowid := some 1 } := by decide +kernel

/-- A program that fails with {lit}`RAISE(ABORT)` after a nested insert: the statement changes none,
the completed nested insert counts for the total, and the last rowid keeps the rowid of the row
that the statement inserted before the failure. -/
example : countersUnder defaults (tables ++ [afterInsert [logged (.numeric "1"), selected (.raise .abort (some (text "no")))],
    insertSeven]) = { changes := some 0, totalChanges := some 1, lastInsertRowid := some 1 } := by decide +kernel

/-- A program that fails with {lit}`RAISE(FAIL)` on the second of three rows: the statement keeps
the two rows that it reached, and the one nested insert counts for the total. -/
example : countersUnder defaults (tables ++ [afterInsert [logged (.numeric "1"), selected (.raise .fail (some (text "no")))] true,
    insertT [[.null, .numeric "7"], [.null, .numeric "8"], [.null, .numeric "9"]]]) =
    { changes := some 2, totalChanges := some 3, lastInsertRowid := some 2 } := by decide +kernel

/-- A DELETE whose cascade deletes a child row: the statement changes one row, and the cascade adds
one to the total only. The two inserts of the schema set the last rowid to the rowid 1 of the child. -/
example : countersOfRun ForeignKeyExamples.keysOn (ForeignKeyExamples.schema .cascade .noAction ++ [ForeignKeyExamples.deleteOne]) =
    { changes := some 1, totalChanges := some 5, lastInsertRowid := some 1 } := by decide +kernel

/-- A DROP TABLE of a table that a child references with a cascade: the statement changes the two
rows of the table, and the total adds them with the one row of the cascade. -/
example : countersOfRun ForeignKeyExamples.keysOn
    (ForeignKeyExamples.schema .cascade .noAction ++ [.dropTable (name! "p") false]) =
    { changes := some 2, totalChanges := some 6, lastInsertRowid := some 1 } := by decide +kernel

/-- A single-row INSERT without a parent fails before it stores the row: it changes none, and
leaves the last rowid at the rowid 1 of the earlier child. -/
example : countersOfRun ForeignKeyExamples.keysOn (plainSchema ++ [insertChildren ["9"]]) =
    { changes := some 0, totalChanges := some 3, lastInsertRowid := some 1 } := by decide +kernel

/-- A trigger of the DELETE of a REPLACE that fails with {lit}`RAISE(FAIL)`: the statement keeps the
delete and not the new row. It changes none, because the row that REPLACE deletes is no changed row,
and the total keeps the one row of the earlier INSERT. -/
example : countersOfRun recursiveOn (replaceWithDeleteTrigger [selected (.raise .fail (some (text "no")))]) =
    { changes := some 0, totalChanges := some 1, lastInsertRowid := some 1 } := by decide +kernel

/-- The same trigger with a nested insert before the failure: the nested insert counts for the
total. -/
example : countersOfRun recursiveOn
    (replaceWithDeleteTrigger [logged (.numeric "1"), selected (.raise .fail (some (text "no")))]) =
    { changes := some 0, totalChanges := some 2, lastInsertRowid := some 1 } := by decide +kernel

end Belay.Sqlite.Model.CounterRowExamples
