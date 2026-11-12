import Belay.Sqlite.Model.Programs.Scripts.ScriptRun
import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyCheckExamples

set_option doc.verso true

/-! Examples of {lit}`PRAGMA foreign_key_check` (ADR 0019, D2), each checked by the kernel. With
foreign keys off, the writes store child rows without a parent, which the pragma reports. The
rows and errors are SQLite's (3.51.0, checked natively with the {lit}`sqlite3` shell). The order of
the rows shows in {name}`Belay.Sqlite.Model.Database.foreignKeyCheckRows`; a query without
{lit}`ORDER BY` gives them in normal form. -/

namespace Belay.Sqlite.Model.ForeignKeyCheckExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- The outputs of a run of the statements from the empty database, with the default profile. -/
def outputs (script : List Syntax.Statement) : List Output :=
  (runScriptFrom { profile := defaults, mode := .execution } none 0 { state := { database := {} } }
    (script.map (·, []))).outputs

example : outputs (orphans ++ [.pragma (.foreignKeyCheck (some (name! "C2"))), .pragma (.foreignKeyCheck (some (name! "p")))]) =
    [.done 0, .done 0, .done 1, .done 0, .done 2, .rows [keyRow "c2" (some 1) "q" 0], .rows []] := by decide +kernel
-- Without a table name, two tables with rows give no result; a missing table fails at prepare.
example : (outputs (orphans ++ [.pragma (.foreignKeyCheck none)])).getLast?.map Output.endsRun = some true := by
  decide +kernel
example : (outputs [.pragma (.foreignKeyCheck (some (name! "nosuch")))]) = [.error 1] := by decide +kernel

end Belay.Sqlite.Model.ForeignKeyCheckExamples
