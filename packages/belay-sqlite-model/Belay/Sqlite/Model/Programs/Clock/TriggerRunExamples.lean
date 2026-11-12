import Belay.Sqlite.Model.Programs.Clock.SqlExecution
import Belay.Sqlite.Model.Schema.Triggers.TriggerRunExamples

set_option doc.verso true

/-! Examples of the triggers that writes run (ADR 0018, D5), each checked by the kernel: the times
and events with {lit}`NEW` and {lit}`OLD`, the order of two triggers, {lit}`WHEN`, {lit}`UPDATE OF`,
each {lit}`RAISE`, a trigger that would fire itself, REPLACE, a foreign-key action that fires a
trigger, and the change count. The cases follow native SQLite 3.51.0, and the authored corpus of
the slice checks them against it. -/

namespace Belay.Sqlite.Model.TriggerRunExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- The log after the script with a trigger that logs {lit}`CURRENT_TIMESTAMP`, under a clock of
Julian day 2460000 for every statement. -/
def clockLog : List (List Value) :=
  let script := statements (migration [] (tables ++ [trigger "a" .after .insert [logged (.currentTime "CURRENT_TIMESTAMP")],
    insertT [[.null, .numeric "1"]]]))
  ((runSqlAt (fun _ => 2460000 * 86400000) (bindValues script []) {}).database.rows.getD 1 []).map (·.values)

-- A statement whose trigger reads the clock reads it: the trigger logs the time, not NULL.
#guard clockLog.all fun row => row.all (· matches .text _)
#guard clockLog.length == 1

end Belay.Sqlite.Model.TriggerRunExamples
