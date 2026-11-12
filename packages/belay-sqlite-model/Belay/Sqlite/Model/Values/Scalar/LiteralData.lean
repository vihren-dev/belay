set_option doc.verso true

namespace Belay.Sqlite.Model
namespace LiteralData

/-- Check SQLite's signed 64-bit range for literals and stored comparison keys.
{assert}`boundedInteger 0 = true`; the upper bound itself is excluded. -/
def boundedInteger (value : Int) : Bool := decide (-(2 ^ 63 : Int) ≤ value ∧ value < 2 ^ 63)

end LiteralData
end Belay.Sqlite.Model
