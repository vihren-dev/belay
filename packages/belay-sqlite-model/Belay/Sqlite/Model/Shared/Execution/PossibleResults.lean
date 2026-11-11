import Belay.Sqlite.Model.Shared.Execution.Execution
import Belay.Sqlite.Model.Shared.Execution.QueryEval

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- A total order of values: {name}`Value.compare`, and among the values that it says are equal
but differ, NULL first, an integer before a real, and reals by their bits, so that a NaN REAL,
which the model never makes, is not equal to NULL either. For example, the integer 1 comes
before the real 1.0. -/
def compareNormal (first second : Value) : Ordering :=
  (Value.compare first second).then (match first, second with
    | .integer _, .real _ => .lt
    | .real _, .integer _ => .gt
    | .real a, .real b => compare a b
    | .null, .integer _ | .null, .real _ | .null, .text _ | .null, .blob _ => .lt
    | .integer _, .null | .real _, .null | .text _, .null | .blob _, .null => .gt
    | .null, .null | .integer _, .integer _ | .integer _, .text _ | .integer _, .blob _
    | .real _, .text _ | .real _, .blob _
    | .text _, .integer _ | .text _, .real _ | .text _, .text _ | .text _, .blob _
    | .blob _, .integer _ | .blob _, .real _ | .blob _, .text _ | .blob _, .blob _ => .eq)

/-- The order of two rows: column by column by {name}`compareNormal`, a shorter row first when
one is a prefix of the other. -/
def compareRows : List Value → List Value → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | first :: rest, other :: others => (compareNormal first other).then (compareRows rest others)

/-- The normal form of rows whose order SQLite does not promise: sorted by {name}`compareRows`. -/
def normalForm (rows : List (List Value)) : List (List Value) :=
  stableSort (fun a b => (compareRows a b).isLE) rows

end Belay.Sqlite.Model.Resolved
