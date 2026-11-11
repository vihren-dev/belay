import Belay.Sqlite.Model.Programs.Scripts.ScriptRun
import Belay.Sqlite.Model.Schema.Rows.PragmaCheckExamples

set_option doc.verso true

/-! Examples of {lit}`PRAGMA integrity_check` and {lit}`PRAGMA quick_check` (ADR 0019, D2), each
checked by the kernel. No statement of the model writes a row that fails a constraint, so each
failing database comes from a script and then gets rows that no statement writes, as a pragma
such as {lit}`writable_schema` or another program could. The rows are SQLite's (3.51.0, checked
natively with the {lit}`sqlite3` shell on such databases). The order of the rows shows in
{name}`Belay.Sqlite.Model.Database.checkRows`; a query without {lit}`ORDER BY` gives them in normal form. -/

namespace Belay.Sqlite.Model.PragmaCheckExamples

open Belay.Sqlite.Model Syntax Resolution.Examples ValidityExamples

/-- The outputs of a run of the statements from the database, with the default profile. -/
def outputsOn (database : Database) (script : List Syntax.Statement) : List Output :=
  (runScriptFrom { profile := defaults, mode := .execution } none 0 { state := { database } }
    (script.map (·, []))).outputs

-- The limit keeps the first rows; the statement gives them in normal form. The table name is
-- folded, and a missing table fails at prepare.
example : outputsOn brokenT [.pragma (.check false 2 (some (name! "T"))), .pragma (.check true 0 (some (name! "nosuch")))] =
    [.rows (textRows ["CHECK constraint failed in t", "NULL value in t.a"]), .error 1] := by decide +kernel
example : (outputsOn {} [.pragma (.check false 0 (some (name! "sqlite_schema")))]).map Output.endsRun = [true] := by
  decide +kernel

-- The form with a table name checks only that table; the form without one gives the rows of
-- the one failing table, and no result when two tables fail.
example : outputsOn brokenP [.pragma (.check false 0 (some (name! "q"))), .pragma (.check true 0 none)] =
    [.rows (textRows ["ok"]), .rows (textRows ["NULL value in p.a"])] := by decide +kernel
example : (outputsOn (brokenP.setRows 1 [stored 1 [.null]]) [.pragma (.check false 0 none)]).map Output.endsRun =
    [true] := by decide +kernel

-- After writes, both checks give ok.
example : outputsOn {} [.createTable (name! "v") [typed "a" none [.notNull, .unique]] [],
    .insert (name! "v") none [[.numeric "1"], [.numeric "2"]] [], .pragma (.check false 0 none),
    .pragma (.check true 5 (some (name! "v")))] = [.done 0, .done 2, .rows (textRows ["ok"]), .rows (textRows ["ok"])] := by
  decide +kernel

end Belay.Sqlite.Model.PragmaCheckExamples
