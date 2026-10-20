import VerifierConformance.Pass
import Belay.Sqlite.QueryExamples

set_option doc.verso true

/-! Checked examples of a query statement in a script (ADR 0012): it changes nothing,
the script continues, and its output is the result column names and rows. A write with
{lit}`RETURNING` (slice 3a) outputs its change count and one row for each written row. -/

namespace Belay.Sqlite.Conformance.QueryOutputs

open Resolved.QueryExamples in
/-- A database with the example table of {lit}`Belay.Sqlite.Resolved.QueryExamples`
at catalog position 0. -/
def database : Database := .ofTables [((name! "t"), table)]

#guard match advance 0 (.query Resolved.QueryExamples.grouped []) { database } with
  | .next next => next.database.table 0 == database.table 0 && next.snapshot.isNone
  | .halt _ => false
#guard (passFrom 0 [.query Resolved.QueryExamples.plain []] { database }).outputs ==
  [some ⟨["v"], [[.text [97]], [.text [98]], [.text [99]], [.text [100]]], none⟩]
-- A query whose table is missing has no output.
#guard (passFrom 0 [.query { Resolved.QueryExamples.plain with sources := [.first 5] } []] { database }).outputs == [none]
-- INSERT ... RETURNING v, k + 1 returns the inserted row.
#guard (passFrom 0 [.insert 0 [[.value (.integer 5), .value (.text [101])]]
    [(.column 1, "v"), (.arithmetic .add (.column 0) (.literal (.integer 1)), "k + 1")]] { database }).outputs ==
  [some ⟨["v", "k + 1"], [[.text [101], .integer 6]], some 1⟩]
-- UPDATE ... SET v = 'z' WHERE k = 1 RETURNING v returns the new values of the two matched rows.
#guard (passFrom 0 [.update 0 [(1, .literal (.text [122]))] (some (.compare .eq none (.column 0) (.literal (.integer 1))))
    [(.column 1, "v")]] { database }).outputs ==
  [some ⟨["v"], [[.text [122]], [.text [122]]], some 2⟩]

open Resolved.QueryExamples in
-- DELETE ... RETURNING v without a filter returns the old value of every row, in rowid order,
-- and counts them.
#guard (passFrom 0 [.delete 0 none [(.column 1, "v")]] { database }).outputs ==
  [some ⟨["v"], table.scanRows.map (fun row => [row.values.getD 1 .null]), some table.rows.length⟩]

end Belay.Sqlite.Conformance.QueryOutputs
