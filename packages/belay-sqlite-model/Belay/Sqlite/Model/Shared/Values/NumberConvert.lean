set_option doc.verso true

namespace Belay.Sqlite.Model

/-- SQLite's {lit}`sqlite3RealToI64`: a double to a 64-bit integer, saturated at the
limits and truncated toward zero. A NaN passes both limit tests and gives the smallest
64-bit integer, as the conversion instruction of x86-64 does; SQLite stores no NaN, so
only an intermediate value can be one. -/
def realToI64 (value : Float) : Int :=
  if value < -9223372036854774784.0 then -(2 ^ 63)
  else if value > 9223372036854774784.0 then 2 ^ 63 - 1
  else if value.isNaN then -(2 ^ 63)
  else if value < 0 then -((-value).toUInt64.toNat : Int)
  else (value.toUInt64.toNat : Int)

end Belay.Sqlite.Model
