import Belay.Sqlite.Model.Programs.Clock.TriggerRunExamples
import Belay.Sqlite.Model.Programs.Scripts.ScriptRun
import Belay.Sqlite.Model.Schema.Triggers.RecursiveTriggerExamples

set_option doc.verso true

/-! Examples of {lit}`PRAGMA recursive_triggers` (ADR 0019, D2), each checked by the kernel: a
trigger that fires itself with the setting on and off, the depth limit of the profile, also for
a program whose {lit}`WHEN` condition is false, the DELETE triggers of the rows that REPLACE
deletes, whose programs inherit REPLACE, the setting of the profile at the start of a script,
the setting inside a transaction, and the query form. The cases follow native SQLite 3.51.0, with
{lit}`.limit trigger_depth 3` in the shell for the depth limit. -/

namespace Belay.Sqlite.Model.RecursiveTriggerExamples

open Belay.Sqlite.Model Syntax Resolution.Examples TriggerRunExamples

/-- The outputs of a run of the statements from the empty database with the profile. -/
def outputsWith (profile : Profile) (script : List Syntax.Statement) : List Output :=
  (runScriptFrom { profile, mode := .execution } none 0 { state := { database := {} } } (bindValues script [])).outputs

example : (outputsWith shallow (tables ++ [recursiveOn, chain "4", insertOne])).getLast? matches some (.unmodeled _) := by
  decide +kernel

-- The query gives one row with the column recursive_triggers: 0 on an idle connection, and 1
-- after the pragma turns the setting on.
example : outputsWith defaults [.pragma (.setting .recursiveTriggers none), recursiveOn,
    .pragma (.setting .recursiveTriggers none)] = [.rows [[.integer 0]], .done 0, .rows [[.integer 1]]] := by
  decide +kernel

end Belay.Sqlite.Model.RecursiveTriggerExamples
