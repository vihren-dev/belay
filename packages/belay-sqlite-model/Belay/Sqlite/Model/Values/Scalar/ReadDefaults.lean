import Belay.Sqlite.Model.Values.Scalar.StoreValue
import Belay.Sqlite.Model.Values.Scalar.Values

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Read a numeric default using SQLite's literal-value path. Decimal text that
is not an in-range unsigned integer keeps its spelling under TEXT affinity.
An oversized hexadecimal token stays text, while unary minus converts that text
to zero. Negating the hexadecimal minimum integer produces a REAL value.
Separators are removed as the parser does. For example,
{lean}`readNumericDefault .text "1.50" false` reads the spelling {lit}`1.50`
for a TEXT column.
Use {name}`queryNumeric` for INSERT expression evaluation instead. -/
def readNumericDefault (affinity : Affinity) (token : String) (negated : Bool) : Value :=
  let text := String.ofList (token.toList.filter (· ≠ '_'))
  let value := match numericValue text false with
    | .integer integer =>
      if negated then
        if integer == -(2 ^ 63 : Int) then realValue 9223372036854775808.0
        else .integer (-integer)
      else .integer integer
    | .hexTooBig => if negated then .integer 0 else .text text.toUTF8.toList
    | .real =>
      let bytes := ((if negated then "-" else "") ++ text).toUTF8.toList
      if affinity == .blob then
        if text.toList.any (fun c => c == '.' || c == 'e' || c == 'E') then realLiteral text.toList negated
        else numericText bytes
      else .text bytes
  Value.store affinity value

end Belay.Sqlite.Model
