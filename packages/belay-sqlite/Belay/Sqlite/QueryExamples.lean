import Belay.Sqlite.QueryEval

set_option doc.verso true

/-! Checked examples of query evaluation (ADR 0012, slice 1) over one small table.
Native SQLite is the authority for these rules; the conformance cases compare them
with it. These examples fix the intended reading of each step. -/

namespace Belay.Sqlite.Resolved.QueryExamples

/-- A table {lit}`t(k, v)` with rows in an order other than rowid order: rowid 3 has
NULL, rowids 1 and 2 have the key 1, rowid 4 has the key 2. -/
def table : Table where
  shape := { columns := [{ name := "k", declaredType := none }, { name := "v", declaredType := none }] }
  rows := [⟨3, [.null, .text [99]]⟩, ⟨1, [.integer 1, .text [97]]⟩, ⟨2, [.integer 1, .text [98]]⟩,
    ⟨4, [.integer 2, .text [100]]⟩]

/-- {lit}`SELECT v FROM t`: one row per table row, without a defined order. -/
def plain : Query where
  table := 0
  filter := none
  aggregate := false
  groupBy := []
  columns := [.scalar (.column 1)]
  names := ["v"]
  orderBy := []
  offset := 0
  limit := none

#guard plain.run table == [[.text [97]], [.text [98]], [.text [99]], [.text [100]]]
-- WHERE k = 1 keeps the rows whose comparison is true; NULL = 1 is NULL, not true.
#guard { plain with filter := some (.compare .eq (.column 0) (.literal (.integer 1))) }.run table ==
  [[.text [97]], [.text [98]]]
-- ORDER BY k DESC puts NULL last; the tie between rowids 1 and 2 keeps rowid order.
#guard { plain with orderBy := [(.expression (.column 0), true)] }.run table ==
  [[.text [100]], [.text [97]], [.text [98]], [.text [99]]]
-- ORDER BY k with LIMIT 2 OFFSET 1: NULL first, then the window.
#guard { plain with orderBy := [(.expression (.column 0), false)], offset := 1, limit := some 2 }.run table ==
  [[.text [97]], [.text [98]]]
/-- {lit}`SELECT k, COUNT(*), MIN(v), COUNT(k) FROM t GROUP BY k ORDER BY 1`. -/
def grouped : Query where
  table := 0
  filter := none
  aggregate := true
  groupBy := [.column 0]
  columns := [.scalar (.column 0), .aggregate .countRows, .aggregate (.min (.column 1)), .aggregate (.count (.column 0))]
  names := ["k", "count(*)", "min(v)", "count(k)"]
  orderBy := [(.output 0, false)]
  offset := 0
  limit := none

#guard grouped.run table ==
  [[.null, .integer 1, .text [99], .integer 0], [.integer 1, .integer 2, .text [97], .integer 2],
   [.integer 2, .integer 1, .text [100], .integer 1]]
-- An aggregate query without GROUP BY gives one row, also for an empty table.
#guard { plain with aggregate := true, columns := [.aggregate .countRows, .aggregate (.max (.column 0))] }.run
  { table with rows := [] } == [[.integer 0, .null]]

end Belay.Sqlite.Resolved.QueryExamples
