import Belay.Sqlite.Model.Queries.Preparation.ScriptRunExamples
import Belay.Sqlite.Model.Shared.Resolved.Context

set_option doc.verso true

namespace Belay.Sqlite.Model.InsertSelectExamples

open Belay.Sqlite.Model Syntax Resolution.Examples ScriptRunExamples

/-- The context of the examples: the default profile, in execution mode. -/
def context : ResolveContext := { profile := defaults, mode := .execution }

/-- {lit}`SELECT last_insert_rowid()`. -/
def lastRowid : Syntax.Statement := selectOf (.call "last_insert_rowid" [])

end Belay.Sqlite.Model.InsertSelectExamples
