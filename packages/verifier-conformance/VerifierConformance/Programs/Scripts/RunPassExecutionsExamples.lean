import VerifierConformance.Programs.Clock.Classify
import Belay.Sqlite.Model.Programs.Scripts.CounterReadExamples
import Belay.Sqlite.Model.Schema.Triggers.CounterReadExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Conformance.RunPassExecutionsExamples

open Belay.Sqlite.Model

/-- A new connection with the counters at 0. -/
def start : Connection := { state := { database := {}, counters := Counters.newConnection } }

end Belay.Sqlite.Model.Conformance.RunPassExecutionsExamples
