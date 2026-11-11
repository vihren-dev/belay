import Belay.Sqlite.Model.Programs.Scripts.ScriptRunExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.ScriptRunExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- {lit}`2025-01-01 00:00:00` in Julian-day milliseconds, at every index. -/
def newYear : Option Clock := some fun _ => 212602449600000

/-- {lit}`CREATE TABLE c(a TEXT, b DEFAULT CURRENT_TIMESTAMP)`. -/
def createClocked : Syntax.Statement :=
  .createTable (name! "c") [column (name! "a"),
    { name := name! "b", declaredType := none,
      constraints := [.default (.currentTime "CURRENT_TIMESTAMP") "CURRENT_TIMESTAMP"] }] []

-- With a clock, CURRENT_TIMESTAMP and date('now') give the text of the clock's time, as SQLite does.
example : outputs [selectOf (.currentTime "CURRENT_TIMESTAMP"), selectOf (.call "date" [.string "now".toUTF8.toList])]
    (clock := newYear) = [.rows [[textValue "2025-01-01 00:00:00"]], .rows [[textValue "2025-01-01"]]] := by
  decide +kernel

-- With a clock, an INSERT gives a DEFAULT of CURRENT_TIMESTAMP the text of the clock's time.
example : outputs [createClocked, insertClocked, selectClocked] (clock := newYear) =
    [.done 0, .done 1, .rows [[textValue "2025-01-01 00:00:00"]]] := by
  decide +kernel

-- Without a clock, each of these statements ends the run; the statements after it do not run.
example : outputs [selectOf (.currentTime "CURRENT_TIMESTAMP"), selectNames] = [.unmodeled clockUnmodeled] := by
  decide +kernel
example : outputs [selectOf (.call "date" [.string "now".toUTF8.toList])] = [.unmodeled clockUnmodeled] := by
  decide +kernel
example : outputs [createClocked, insertClocked, selectClocked] = [.done 0, .unmodeled clockUnmodeled] := by
  decide +kernel

end Belay.Sqlite.Model.ScriptRunExamples
