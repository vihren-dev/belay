import Belay.Sqlite.Queries.Evaluation.ReadAnalysis

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- A calm statement is decided by the check of each of its expressions ({name}`Resolved.Expr.Calm`). -/
instance (statement : Resolved.Statement) : Decidable statement.Calm :=
  inferInstanceAs (Decidable (∀ expression ∈ statement.clockExpressions, expression.Calm))

/-- The cells of a row that NOT NULL columns forbid to be NULL: with one flag for each column, true for
a NOT NULL column, each cell under a true flag is not NULL. Cells past the flags, and flags past the
cells, require nothing. -/
def NotNullCells : List Bool → List Value → Prop
  | true :: flags, value :: values => value ≠ .null ∧ NotNullCells flags values
  | false :: flags, _ :: values => NotNullCells flags values
  | [], _ | _ :: _, [] => True

end Belay.Sqlite
