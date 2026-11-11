import Lean.Elab.DocString
import Belay.Sqlite.Schema.Dispatch.EvalDatabase
import Belay.Sqlite.Programs.Clock.Env
import Belay.Sqlite.Programs.Scripts.Run

set_option doc.verso true

namespace Belay.Sqlite.SqlDoc

open Lean Elab Term Meta Belay.Sqlite

/-- The type {lit}`List Output`, the complete observation of a script. -/
def outputsType : Expr := mkApp (mkConst ``List [Level.zero]) (mkConst ``Output)

end Belay.Sqlite.SqlDoc
