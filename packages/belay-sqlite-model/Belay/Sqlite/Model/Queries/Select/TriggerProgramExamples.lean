import Belay.Sqlite.Model.Queries.Fixtures.Examples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.TriggerProgramExamples

open Belay.Sqlite.Model Syntax

/-- {lit}`SELECT result` in a body. -/
def selected (result : Expr) (filter : Option Expr := none) : BodyStatement :=
  .select [.expression result none ""] none [] filter [] [] none none

end Belay.Sqlite.Model.Resolution.TriggerProgramExamples
