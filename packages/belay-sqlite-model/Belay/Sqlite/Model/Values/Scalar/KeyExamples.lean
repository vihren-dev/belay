import Belay.Sqlite.Model.Shared.Values.Declarations

set_option doc.verso true

namespace Belay.Sqlite.Model.KeyExamples
open Belay.Sqlite.Model

/-- The REAL value {lit}`1.0`. -/
def realOne : Value := .real 0x3FF0000000000000

end Belay.Sqlite.Model.KeyExamples
