import Belay.Sqlite.Model.Programs.Scripts.CounterExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.CounterExamples

open Belay.Sqlite.Model ScriptRunExamples

/-- A failed INSERT changes none, adds none to the total, and keeps the rowid 3 of the row that it
stored before the failing row. -/
example : countersAfter [createT, insertT "1" "a", insertT "5" "b", insertFailing] =
    { changes := some 0, totalChanges := some 2, lastInsertRowid := some 3 } := by
  decide +kernel

/-- An UPDATE of two rows changes two and adds two to the total, and keeps the last rowid. -/
example : countersAfter [createT, insertTwo, updateAll] =
    { changes := some 2, totalChanges := some 4, lastInsertRowid := some 9 } := by
  decide +kernel

/-- A DELETE of one row changes one and adds one to the total, and keeps the last rowid. -/
example : countersAfter [createT, insertTwo, deleteFive] =
    { changes := some 1, totalChanges := some 3, lastInsertRowid := some 9 } := by
  decide +kernel

/-- An upsert that takes the {lit}`DO UPDATE` branch changes one row and adds one to the total, and
leaves the last rowid: the updated row is no inserted row. -/
example : countersAfter [createT, insertTwo, upsertUpdate] =
    { changes := some 1, totalChanges := some 3, lastInsertRowid := some 9 } := by
  decide +kernel

/-- An upsert that skips one row and inserts the other changes one row, adds one to the total, and
sets the last rowid to the rowid 11 of the inserted row. -/
example : countersAfter [createT, insertTwo, upsertSkipping] =
    { changes := some 1, totalChanges := some 3, lastInsertRowid := some 11 } := by
  decide +kernel

/-- An {lit}`INSERT OR IGNORE` that skips its only row changes none, adds none to the total, and
leaves the last rowid. -/
example : countersAfter [createT, insertTwo, insertT "5" "q" (some .ignore)] =
    { changes := some 0, totalChanges := some 2, lastInsertRowid := some 9 } := by
  decide +kernel

end Belay.Sqlite.Model.CounterExamples
