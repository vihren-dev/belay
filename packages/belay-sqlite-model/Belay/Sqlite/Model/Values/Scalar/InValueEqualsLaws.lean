import Belay.Sqlite.Model.Values.Scalar.StoreValueLaws

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- For all bits, {name}`integerAffinity` gives a number, not NULL. Proof sketch: it gives an integer
or a REAL. -/
theorem integerAffinity_isNull (bits : UInt64) : (integerAffinity bits).isNull = false := by
  unfold integerAffinity; split <;> rfl

/-- For all text bytes, the number-or-text of {name}`numericText` is not NULL. Proof sketch: the
text stays text, or {name}`textNumber` gives an integer or the result of {name}`integerAffinity`. -/
theorem numericText_isNull (bytes : List UInt8) : (numericText bytes).isNull = false := by
  unfold numericText textNumber
  rcases atof bytes with ⟨double, code⟩
  dsimp only
  split
  · rfl
  · split
    · rfl
    · exact integerAffinity_isNull _

/-- For every value, {name}`numericStore` gives NULL exactly for NULL. Proof sketch: a REAL becomes
the result of {name}`integerAffinity`, a text the result of {name}`numericText`, and the others stay. -/
theorem numericStore_isNull (value : Value) : (numericStore value).isNull = value.isNull := by
  cases value
  case real bits => exact integerAffinity_isNull bits
  case text bytes => exact numericText_isNull bytes
  all_goals rfl

/-- For every value, {name}`realRead` gives NULL exactly for NULL. Proof sketch: a number becomes a
REAL, and the others stay. -/
theorem realRead_isNull (value : Value) : (realRead value).isNull = value.isNull := by
  cases value <;> rfl

end Belay.Sqlite.Model.Resolved
