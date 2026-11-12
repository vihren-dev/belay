import Belay.Sqlite.Shared.Execution.Script
import Belay.Sqlite.Schema.Rows.Database
import Belay.Sqlite.Model.Frontend.Codecs.Codec

set_option doc.verso true

namespace Belay.Sqlite

/-- The context in which the surface resolves the statements of a run: the pinned profile
({name}`Profile.pinned`), with statements that run. -/
def runContext : Belay.Sqlite.Model.ResolveContext := { profile := Profile.pinned, mode := .execution }

end Belay.Sqlite
