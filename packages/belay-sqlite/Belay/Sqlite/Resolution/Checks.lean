import Belay.Sqlite.Resolution.ResolvedExprForm

set_option doc.verso true

/-! The CHECK constraints of a table (ADR 0014, D2). A CHECK is a condition over a row of
its table, resolved once when the table is defined, and the label that SQLite reports
when the condition is false. Execution checks it on every row that a write stores. -/

namespace Belay.Sqlite

/-- One CHECK constraint: its condition over a row of the table and the label of
{lit}`CHECK constraint failed: label`. For example, {lit}`CHECK (a > 0)` on the first
column has the condition {lean}`Resolved.Expr.compare .gt none (.column 0) (.literal (.integer 0))`
and the label {lit}`a > 0`. -/
structure CheckConstraint where
  /-- The condition over the row, resolved as a {lit}`WHERE` condition of the table. -/
  condition : Resolved.Expr
  /-- The label that SQLite reports when the condition is false. -/
  label : String
  deriving Repr, DecidableEq

end Belay.Sqlite
