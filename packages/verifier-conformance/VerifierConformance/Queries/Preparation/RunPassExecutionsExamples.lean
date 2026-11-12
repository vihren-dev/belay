import Belay.Sqlite.Model.Queries.Preparation.ScriptRunExamples
import Belay.Sqlite.Model.Queries.Preparation.CounterReadExamples
import Belay.Sqlite.Model.Shared.Resolved.Context

set_option doc.verso true

namespace Belay.Sqlite.Model.Conformance.RunPassExecutionsExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- The context of the examples: the default profile, in execution mode. -/
def context : ResolveContext := { profile := defaults, mode := .execution }

/-- {lit}`PRAGMA foreign_keys = ON`, then {lit}`SELECT changes()`. -/
def script : List Syntax.Statement :=
  [.pragma (.setting .foreignKeys (some true)), .select [.expression (.call "changes" []) none "changes()"] none [] none [] [] none none]

end Belay.Sqlite.Model.Conformance.RunPassExecutionsExamples
