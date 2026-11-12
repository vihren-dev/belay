import Belay.Sqlite.Model.Shared.Execution.Execution
import Belay.Sqlite.Model.Queries.Evaluation.QueryExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved.SubqueryExamples

open QueryExamples (table)

/-- A table {lit}`u(x)` with the rows 1, NULL and 3, in rowid order. -/
def other : Table where
  shape := { columns := [{ name := (name! "x"), declaredType := none }] }
  rows := [⟨1, [.integer 1]⟩, ⟨2, [.null]⟩, ⟨3, [.integer 3]⟩]

/-- The database with {lit}`t` of {lit}`Belay.Sqlite.Model.Resolved.QueryExamples` at catalog position
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
  { keysWhere (.literal .null) with sources := [.first 1], filter, columns := [.scalar result], names := ["r"], outer := 2 }

/-- {lit}`u.x = t.k` inside a subquery over {lit}`u` directly under {lit}`t`. -/
def matchesKey : Expr := .compare .eq none (.column 2) (.column 0)

/-- {lit}`SELECT (q) FROM t` for a scalar subquery {lit}`q`. -/
def scalarOf : Query := { keysWhere (.literal (.integer 1)) with filter := none, columns := [.scalar (.subquery 0)] }

/-- {lit}`(SELECT x FROM u ORDER BY x DESC LIMIT 1)`: the largest value, without a tie. -/
def largest : Query :=
  { fromOther (.column 2) none with orderBy := [{ key := .expression (.column 2), descending := true }], limit := some 1 }

end Belay.Sqlite.Model.Resolved.SubqueryExamples
