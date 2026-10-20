import Belay.Sqlite.Resolution.ResolvedExprForm

set_option doc.verso true

/-! The CHECK constraints and the generated columns of a table (ADR 0014, D2 and D5). A
CHECK is a condition over a row of its table, resolved once when the table is defined,
and the label that SQLite reports when the condition is false. Execution checks it on
every row that a write stores, after it computes the generated columns of the row. -/

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

/-- How a generated column is computed: its expression over a row of the table and whether
it is {lit}`STORED`. For example, {lit}`b AS (a * 2)` on a table {lit}`(a, b)` has the expression
{lean}`Resolved.Expr.arithmetic .multiply (.column 0) (.literal (.integer 2))` and is
{lit}`VIRTUAL`. The model stores the values of both kinds, as they read the same (ADR 0014,
D5). -/
structure GeneratedColumn where
  /-- The expression over a row of the table. -/
  expression : Resolved.Expr
  /-- Whether the column is {lit}`STORED`; false for {lit}`VIRTUAL`. -/
  stored : Bool
  deriving Repr, DecidableEq

end Belay.Sqlite
