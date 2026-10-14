import Belay.Sqlite.StoreValue

set_option doc.verso true

/-! Laws of store-time affinity (ADR 0012, amendment 1, "Proofs"): storing a stored value
again changes nothing, which is the key lemma for the stored form of {lit}`Conforms`, and
TEXT affinity never stores a number. -/

namespace Belay.Sqlite

/-- For all bits, {name}`positiveZero` applied twice equals {name}`positiveZero` applied once. -/
theorem positiveZero_positiveZero (bits : UInt64) : positiveZero (positiveZero bits) = positiveZero bits := by
  unfold positiveZero
  split
  · simp [negativeZeroBits]
  · simp

/-- For all bits, {name}`numericStore` of the result of {name}`integerAffinity` is that
result. Proof sketch: an integer stays, and a REAL result has the original bits, for
which {name}`integerAffinity` decides the same way again. -/
theorem numericStore_integerAffinity (bits : UInt64) :
    numericStore (integerAffinity bits) = integerAffinity bits := by
  cases h : wholeReal bits <;> simp [integerAffinity, numericStore, h]

/-- For all text bytes and values: if {name}`textNumber` gives the value, then
{name}`numericStore` keeps it. -/
theorem numericStore_textNumber {bytes : List UInt8} {value : Value} (found : textNumber bytes = some value) :
    numericStore value = value := by
  unfold textNumber at found
  rcases hp : atof bytes with ⟨double, code⟩
  simp only [hp] at found
  split at found
  · cases found
  · split at found <;> cases found
    · rfl
    · exact numericStore_integerAffinity _

/-- For all text bytes, {name}`numericStore` of the result of {name}`numericText` is that
result. Proof sketch: text that is not a number stays the same text, and a number comes
from {name}`textNumber`. -/
theorem numericStore_numericText (bytes : List UInt8) :
    numericStore (numericText bytes) = numericText bytes := by
  cases h : textNumber bytes with
  | none => simp [numericText, numericStore, h]
  | some value => simp only [numericText, h, Option.getD_some]; exact numericStore_textNumber h

/-- For every value, {name}`numericStore` applied twice equals {name}`numericStore` applied
once. -/
theorem numericStore_numericStore (value : Value) : numericStore (numericStore value) = numericStore value := by
  cases value with
  | real bits => exact numericStore_integerAffinity bits
  | text bytes => exact numericStore_numericText bytes
  | null | integer _ | blob _ => rfl

/-- For every value that {name}`numericStore` keeps, {name}`storeValue` with REAL affinity
keeps the result of {name}`realRead`. Proof sketch: a REAL result goes through
{name}`positiveZero` again, which is idempotent; NULL, TEXT and BLOB stay. -/
theorem storeValue_real_realRead (value : Value) (kept : numericStore value = value) :
    storeValue .real (realRead value) = realRead value := by
  cases value with
  | integer _ | real _ => simp only [realRead, storeValue, positiveZero_positiveZero]
  | null | blob _ => rfl
  | text _ => simp only [realRead, storeValue, kept]

/-- For every value that is not a REAL, {name}`storeValue` with REAL affinity is
{name}`realRead` of {name}`numericStore`. -/
theorem storeValue_real_other (value : Value) (other : ∀ bits, value ≠ .real bits) :
    storeValue .real value = realRead (numericStore value) := by
  cases value <;> simp_all [storeValue]

/-- For every affinity and value, {name}`storeValue` applied twice with the affinity equals
{name}`storeValue` applied once: a stored value is in its stored form. Proof sketch: BLOB
and TEXT by cases; NUMERIC and INTEGER by {name}`numericStore_numericStore`; REAL by
{name}`positiveZero_positiveZero` for a REAL value and by {name}`storeValue_real_realRead`
for every other value. -/
theorem storeValue_storeValue (affinity : Affinity) (value : Value) :
    storeValue affinity (storeValue affinity value) = storeValue affinity value := by
  cases affinity with
  | blob => rfl
  | numeric | integer => exact numericStore_numericStore value
  | text => cases value <;> rfl
  | real =>
    cases value with
    | real bits => simp only [storeValue, positiveZero_positiveZero]
    | null => rw [storeValue_real_other .null (by simp)]; exact storeValue_real_realRead _ (numericStore_numericStore _)
    | integer whole =>
      rw [storeValue_real_other (.integer whole) (by simp)]; exact storeValue_real_realRead _ (numericStore_numericStore _)
    | text bytes =>
      rw [storeValue_real_other (.text bytes) (by simp)]; exact storeValue_real_realRead _ (numericStore_numericStore _)
    | blob bytes =>
      rw [storeValue_real_other (.blob bytes) (by simp)]; exact storeValue_real_realRead _ (numericStore_numericStore _)

/-- For every value, {name}`storeValue` with TEXT affinity is not an INTEGER or a REAL. -/
theorem storeValue_text_not_number (value : Value) :
    (∀ whole, storeValue .text value ≠ .integer whole) ∧ (∀ bits, storeValue .text value ≠ .real bits) := by
  cases value <;> simp [storeValue]

end Belay.Sqlite
