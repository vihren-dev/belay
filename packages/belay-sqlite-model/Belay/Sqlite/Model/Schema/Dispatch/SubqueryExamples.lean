import Belay.Sqlite.Model.Schema.Dispatch.Execution
import Belay.Sqlite.Model.Queries.Evaluation.SubqueryExamples

set_option doc.verso true

/-! Checked examples of subqueries over resolved queries (ADR 0018, D1): {lit}`EXISTS`,
{lit}`IN` and scalar subqueries, correlated at depth one and two. Native SQLite is the
authority for these values; the authored subquery corpus compares them with it. A subquery's
row is the outer row followed by its own cells, so in these examples the cells of
{lit}`t(k, v)` are positions 0 and 1, and a subquery's own table starts at position 2. -/

namespace Belay.Sqlite.Model.Resolved.SubqueryExamples

/-- The result rows of a query with its subqueries over the example database, at clock 0. -/
def rowsOf (query : Query) (subqueries : List Query) : Option (List (List Value)) :=
  (query.runOn 0 {} [] database subqueries).map (·.2.rows)

-- EXISTS (SELECT 1 FROM u WHERE u.x = t.k): only the rows whose key is in u.
example : rowsOf (keysWhere (.exists 0)) [fromOther (.literal (.integer 1)) (some matchesKey)] =
    some [[.integer 1], [.integer 1]] := by decide +kernel
-- NOT EXISTS keeps the other rows, also the row whose key is NULL.
#guard rowsOf (keysWhere (.not (.exists 0))) [fromOther (.literal (.integer 1)) (some matchesKey)] ==
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
example : rowsOf (keysWhere (.exists 0))
    [fromOther (.literal (.integer 1)) (some (.and (.compare .eq none (.column 2) (.literal (.integer 3))) (.exists 1))),
     { fromOther (.literal (.integer 1)) (some (.compare .eq none (.column 3) (.column 0))) with outer := 3 }] =
    some [[.integer 1], [.integer 1]] := by decide +kernel

/-- The fault of a query's run with its subqueries over the example database, at clock 0. -/
def faultOf (query : Query) (subqueries : List Query) : Option Fault :=
  (query.runOn 0 {} [] database subqueries).map (·.2.fault)

-- SQLite's plan chooses the first row of (SELECT x FROM u), so the model does not describe its value.
#guard faultOf scalarOf [fromOther (.column 2) none] == some .may
-- One row of an aggregate, and the first row of an order without ties, are certain.
#guard faultOf scalarOf [{ fromOther (.column 2) none with aggregate := true, columns := [.aggregate (.max (.column 2) .binary)] }] ==
  some .none

#guard faultOf scalarOf [largest] == some .none && rowsOf scalarOf [largest] == some (List.replicate 4 [.integer 3])
-- Also in a joined query: SELECT (SELECT x FROM u) FROM t, u AS v, whose subquery's own cell is position 3.
#guard faultOf { scalarOf with sources := [.first 0, { kind := .inner, source := .table 1, condition := none }] }
  [{ fromOther (.column 3) none with outer := 3 }] == some .may
-- IN reads the rows of a window that SQLite's plan chooses: k IN (SELECT x FROM u LIMIT 2).
#guard faultOf (keysWhere (.inQuery (.column 0) 0 none .binary false)) [{ fromOther (.column 2) none with limit := some 2 }] ==
  some .may
-- EXISTS reads only whether a row exists, which no order changes.
#guard faultOf (keysWhere (.exists 0)) [{ fromOther (.column 2) none with limit := some 2 }] == some .none

end Belay.Sqlite.Model.Resolved.SubqueryExamples
