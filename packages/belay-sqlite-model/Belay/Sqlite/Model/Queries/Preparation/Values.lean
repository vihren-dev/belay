import Belay.Sqlite.Model.Queries.Evaluation.Arithmetic
import Belay.Sqlite.Model.Values.Scalar.Arithmetic
import Belay.Sqlite.Model.Shared.Resolved.Values

set_option doc.verso true

/-! Conversion of literal expressions to stored values during name resolution.
Numeric literal text follows SQLite's rules, which are not lexical: separators are
removed, a hexadecimal literal is a 64-bit two's-complement integer, and a decimal
integer outside the 64-bit range is a REAL value. The first scope models no REAL
values and no time functions, so those are model restrictions. -/

namespace Belay.Sqlite.Model

/-- Prefix the paths of model restrictions with the node's position. -/
def ValueIssue.under (prefix_ : List Nat) : ValueIssue → ValueIssue
  | .restriction path reason => .restriction (prefix_ ++ path) reason
  | .prepare error => .prepare error

end Belay.Sqlite.Model
