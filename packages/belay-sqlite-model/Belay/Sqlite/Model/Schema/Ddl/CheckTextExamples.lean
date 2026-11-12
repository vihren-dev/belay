import Belay.Sqlite.Model.Schema.Dispatch.Examples
import Belay.Sqlite.Model.Queries.Preparation.CheckTextExamples

set_option doc.verso true

/-! Examples of the name tokens that a catalog keeps for the text of a CHECK constraint, checked by
{lit}`#guard` when the package builds: a qualifier is bound to the table, a column name to its position
whatever its quotes, a double-quoted string that no column has to nothing, and a constraint name to no text. -/

namespace Belay.Sqlite.Model.Resolution.CheckTextExamples

open Belay.Sqlite.Model Syntax Belay.Sqlite.Model.Resolution.Examples

/-- The checks of the table {lit}`t(a, b)` with one table CHECK of the text. -/
def checksOf (constraint : TableConstraint) : Option (List CheckConstraint) :=
  match (catalogOf (schema [.createTable (name! "t") [column (name! "a"), column (name! "b")] [constraint]])).head? with
  | some { entry := .table table, .. } => some table.checks
  | some { entry := .view _, .. } | some { entry := .index _, .. } | some { entry := .trigger _, .. } | none => none

-- The qualifier stands for the table, the other names for their columns.
#guard (checksOf (.check condition "t.b > 0 and \"a\" < 5" source)).map (·.map (·.source)) ==
  some [some { text := "t.b > 0 and \"a\" < 5", names := [
    { start := 0, stop := 1, quote := .none, target := .table },
    { start := 2, stop := 3, quote := .none, target := .column 1 },
    { start := 12, stop := 15, quote := .double, target := .column 0 }] }]
-- A constraint name gives the label, and the constraint keeps no text.
#guard (checksOf (.check condition "n")).map (·.map (·.source)) == some [none]

end Belay.Sqlite.Model.Resolution.CheckTextExamples
