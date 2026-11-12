import VerifierConformance.Programs.Clock.Classify
import Belay.Sqlite.Model.Programs.Clock.ScriptRunExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Conformance.RunPassExamples

open Belay.Sqlite.Model

/-- The output of a query of the column {lit}`name` that gives the rows. -/
def namesOutput (rows : List ResultRow) : Option StatementOutput :=
  some { columns := ["name"], rows, changes := none }

end Belay.Sqlite.Model.Conformance.RunPassExamples
