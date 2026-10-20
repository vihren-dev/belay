import Belay.Sqlite.Execution
import Belay.Sqlite.QueryExamples

set_option doc.verso true

/-! Checked examples of subqueries over resolved queries (ADR 0018, D1): {lit}`EXISTS`,
{lit}`IN` and scalar subqueries, correlated at depth one and two. Native SQLite is the
authority for these values; the authored subquery corpus compares them with it. A subquery's
row is the outer row followed by its own cells, so in these examples the cells of
{lit}`t(k, v)` are positions 0 and 1, and a subquery's own table starts at position 2. -/

namespace Belay.Sqlite.Resolved.SubqueryExamples

open QueryExamples (table)

/-- A table {lit}`u(x)` with the rows 1, NULL and 3, in rowid order. -/
def other : Table where
  shape := { columns := [{ name := (name! "x"), declaredType := none }] }
  rows := [⟨1, [.integer 1]⟩, ⟨2, [.null]⟩, ⟨3, [.integer 3]⟩]

/-- The database with {lit}`t` of {lit}`Belay.Sqlite.Resolved.QueryExamples` at catalog position
0 and {lit}`u` at position 1. -/
def database : Database := .ofTables [((name! "t"), table), ((name! "u"), other)]

/-- {lit}`SELECT k FROM t WHERE filter`, for a filter that names subqueries. -/
def keysWhere (filter : Expr) : Query where
  sources := [.first 0]
  filter := some filter
  aggregate := false
  groupBy := []
  columns := [.scalar (.column 0)]
  names := ["k"]
  orderBy := []
  offset := 0
  limit := none

/-- {lit}`SELECT result FROM u WHERE filter`, a subquery over {lit}`u`. -/
def fromOther (result : Expr) (filter : Option Expr) : Query :=
  { keysWhere (.literal .null) with sources := [.first 1], filter, columns := [.scalar result], names := ["r"] }

/-- The result rows of a query with its subqueries over the example database, at clock 0. -/
def rowsOf (query : Query) (subqueries : List Query) : Option (List (List Value)) :=
  (query.runOn 0 database subqueries).map (·.2.rows)

/-- {lit}`u.x = t.k` inside a subquery over {lit}`u` directly under {lit}`t`. -/
def matchesKey : Expr := .compare .eq none (.column 2) (.column 0)

-- EXISTS (SELECT 1 FROM u WHERE u.x = t.k): only the rows whose key is in u.
example : rowsOf (keysWhere (.exists 0 false)) [fromOther (.literal (.integer 1)) (some matchesKey)] =
    some [[.integer 1], [.integer 1]] := by decide +kernel
-- NOT EXISTS keeps the other rows, also the row whose key is NULL.
#guard rowsOf (keysWhere (.exists 0 true)) [fromOther (.literal (.integer 1)) (some matchesKey)] ==
  some [[.null], [.integer 2]]
-- k IN (SELECT x FROM u): 1 matches; 2 does not, and u has a NULL, so 2 IN (...) is NULL.
#guard rowsOf (keysWhere (.inQuery (.column 0) 0 none .binary false)) [fromOther (.column 2) none] ==
  some [[.integer 1], [.integer 1]]
-- k NOT IN (SELECT x FROM u) is never true while u has a NULL.
example : rowsOf (keysWhere (.inQuery (.column 0) 0 none .binary true)) [fromOther (.column 2) none] = some [] := by
  decide +kernel
-- Without the NULL row, 2 NOT IN (SELECT x FROM u WHERE x IS NOT NULL) is true; NULL NOT IN (...) stays NULL.
#guard rowsOf (keysWhere (.inQuery (.column 0) 0 none .binary true)) [fromOther (.column 2) (some (.isNull (.column 2) true))] ==
  some [[.integer 2]]
-- A scalar subquery is the first value of the first row: SELECT (SELECT x FROM u) FROM t.
#guard rowsOf { keysWhere (.literal (.integer 1)) with columns := [.scalar (.subquery 0)] } [fromOther (.column 2) none] ==
  some [[.integer 1], [.integer 1], [.integer 1], [.integer 1]]
-- Without a row it is NULL: SELECT (SELECT x FROM u WHERE x > t.k) FROM t gives 3, 3, NULL and 3 in rowid order.
#guard rowsOf { keysWhere (.literal (.integer 1)) with columns := [.scalar (.subquery 0)] }
    [fromOther (.column 2) (some (.compare .gt none (.column 2) (.column 0)))] ==
  some [[.integer 3], [.integer 3], [.null], [.integer 3]]
-- Depth two: EXISTS (SELECT 1 FROM u WHERE u.x = 3 AND EXISTS (SELECT 1 FROM u AS w WHERE w.x = t.k)).
-- The inner subquery's row is t's cells, then u's, then w's: w.x is position 3 and t.k position 0.
example : rowsOf (keysWhere (.exists 0 false))
    [fromOther (.literal (.integer 1)) (some (.and (.compare .eq none (.column 2) (.literal (.integer 3))) (.exists 1 false))),
     { fromOther (.literal (.integer 1)) (some (.compare .eq none (.column 3) (.column 0))) with sources := [.first 1] }] =
    some [[.integer 1], [.integer 1]] := by decide +kernel

end Belay.Sqlite.Resolved.SubqueryExamples
