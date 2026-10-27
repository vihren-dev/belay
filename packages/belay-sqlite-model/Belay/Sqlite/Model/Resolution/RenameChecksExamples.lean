import Belay.Sqlite.Model.Resolution.RenameChecks

set_option doc.verso true

/-! Examples of the rewrite of the text of a CHECK constraint by a rename, checked by {lit}`#guard` when the
package builds. -/

namespace Belay.Sqlite.Model.Resolution.RenameChecksExamples

open Belay.Sqlite.Model Syntax

/-- The text {lit}`t.b > 0` with the tokens of its table qualifier and of its column. -/
def checkText : CheckText :=
  { text := "t.b > 0", names := [
    { start := 0, stop := 1, quote := .none, target := .table },
    { start := 2, stop := 3, quote := .none, target := .column 1 }] }

/-- {lit}`CHECK(t.b > 0)` on the table {lit}`t`: the qualifier is the table and {lit}`b` the column 1. -/
def check : CheckConstraint := { condition := .literal (.integer 1), label := "t.b > 0", source := some checkText }

/-- The label of the constraint after the rename of the target to the name. -/
def labelAfter (target : LabelTarget) (style : RenameStyle) (new : String) : Option String :=
  (check.rename target style (Identifier.ofString new)).map (·.label)

-- A table renamed to a name with a space is written in double quotes; the label is the dequoted text, which ends at the
-- closing quote of the table name, as in SQLite 3.51.0.
#guard labelAfter .table .table "u v" == some "u v"
-- A plain new name stays in the label with the rest of the text.
#guard labelAfter .table .table "u" == some "u"
#guard labelAfter (.column 1) (.column false) "c" == some "t.c > 0"
#guard labelAfter (.column 1) (.column true) "Z z" == some "t.\"Z z\" > 0"
-- A column that the text does not name leaves the text alone.
#guard labelAfter (.column 0) (.column false) "c" == some "t.b > 0"
-- The tokens after the rewritten one move.
#guard ((check.rename (.table) .table (Identifier.ofString "uv")).map fun c => c.source.map fun s =>
  s.names.map fun n => (n.start, n.stop)) == some (some [(0, 4), (5, 6)])
-- A constraint named by CONSTRAINT keeps its label.
#guard (CheckConstraint.rename .table .table (name! "u") { check with source := none }).map (·.label) == some "t.b > 0"
-- The dequote of SQLite.
#guard dequoteLabel "\"a\"\"b\" c" == "a\"b"
#guard dequoteLabel "[a b].c" == "a b"
#guard dequoteLabel "a > 'x'" == "a > 'x'"

end Belay.Sqlite.Model.Resolution.RenameChecksExamples
