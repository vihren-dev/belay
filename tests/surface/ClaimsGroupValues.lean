import Belay

set_option doc.verso true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

/-! The values of a group of an aggregate query through SQL and actual execution: the column
references read the row of the last distinct {lit}`min` or {lit}`max` call, and a result column
that a grouping term names reads the first row of the group. The corpus compares the same
queries with native SQLite. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

namespace GroupValuesExamples

/-- One group under {lit}`NOCASE`: the first row has {lit}`'a'`, the maximum's row {lit}`'A'`,
and {lit}`a+0` is {lit}`1.0` on the first row and {lit}`1` on the others. -/
def database : Database := db! r"
  CREATE TABLE t(a, c TEXT COLLATE NOCASE, n); INSERT INTO t VALUES(1.0, 'a', 1), (1, 'A', 3), (1, 'A', 2);"

/-- With {lit}`max(n)`, the grouped column {lit}`c` and an expression over it read the row of the
maximum. -/
theorem max_row : (database.run (sql r"
    SELECT c, max(n) FROM t GROUP BY c; SELECT c || '', max(n) FROM t GROUP BY c;")).outputs =
    [.rows [[.text "A".toUTF8.toList, .integer 3]], .rows [[.text "A".toUTF8.toList, .integer 3]]] := by
  decide +kernel

/-- The last distinct call decides: {lit}`min` then {lit}`max` reads the maximum's row, and
{lit}`max` then {lit}`min` the minimum's row. -/
theorem last_call_decides : (database.run (sql r"
    SELECT c, min(n), max(n) FROM t GROUP BY c; SELECT c, max(n), min(n) FROM t GROUP BY c;")).outputs =
    [.rows [[.text "A".toUTF8.toList, .integer 1, .integer 3]],
     .rows [[.text "a".toUTF8.toList, .integer 3, .integer 1]]] := by
  decide +kernel

/-- A result column that {lit}`GROUP BY 1` names reads the first row of the group; the same
expression in another column reads the maximum's row. -/
theorem associated_column : (database.run (sql r"
    SELECT a+0, a+0 AS b, max(n) FROM t GROUP BY 1;")).outputs =
    [.rows [[.real (1.0 : Float).toBits, .integer 1, .integer 3]]] := by
  decide +kernel

/-- Without {lit}`min` and {lit}`max`, every expression reads the first row of the group. -/
theorem first_row : (database.run (sql r"SELECT c, count(*) FROM t GROUP BY c;")).outputs =
    [.rows [[.text "a".toUTF8.toList, .integer 3]]] := by
  decide +kernel

/-- For every query without a deciding call and every group, the row of the group is its first
row. Proof sketch: the model law. -/
theorem no_deciding_call (context : Resolved.EvalContext) (query : Resolved.Query) (group : List (List Value))
    (none : query.deciding = none) : query.groupRow context group = group.headD [] :=
  Resolved.Query.groupRow_none none

#print axioms max_row
#print axioms last_call_decides
#print axioms associated_column
#print axioms first_row
#print axioms no_deciding_call

end GroupValuesExamples
