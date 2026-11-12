import Belay.Sqlite.Model.Shared.Values.NumberConvert
import Belay.Sqlite.Model.Shared.Resolved.Operators

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The least 64-bit signed integer. -/
def int64Minimum : Int := -(2 ^ 63)

/-- The greatest 64-bit signed integer. -/
def int64Maximum : Int := 2 ^ 63 - 1

end Belay.Sqlite.Model
