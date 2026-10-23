import Belay.Sqlite.Model.StoreValue

set_option doc.verso true

/-! Laws of store-time affinity (ADR 0012, amendment 1, "Proofs"): storing a stored value
again changes nothing, which is the key lemma for the stored form of {lit}`Conforms`, and
TEXT affinity never stores a number. -/

namespace Belay.Sqlite.Model

/-- For all bits, {name}`positiveZero` applied twice equals {name}`positiveZero` applied once.
Proof sketch: after one application the bits are not {name}`negativeZeroBits`, so the
second application keeps them. -/
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
{name}`numericStore` keeps it. Proof sketch: split on the result code of {name}`atof`;
the value is an integer, which {name}`numericStore` keeps, or a result of
{name}`integerAffinity`, which {name}`numericStore_integerAffinity` covers. -/
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
once. Proof sketch: by cases on the storage class; a REAL uses
{name}`numericStore_integerAffinity`, a TEXT {name}`numericStore_numericText`, and the
other classes do not change. -/
theorem numericStore_numericStore (value : Value) : numericStore (numericStore value) = numericStore value := by
  cases value with
  | real bits => exact numericStore_integerAffinity bits
  | text bytes => exact numericStore_numericText bytes
  | null | integer _ | blob _ => rfl

/-- For every value that {name}`numericStore` keeps, {name}`Value.store` with REAL affinity
keeps the result of {name}`realRead`. Proof sketch: a REAL result goes through
{name}`positiveZero` again, which is idempotent; NULL, TEXT and BLOB stay. -/
theorem Value.store_real_realRead (value : Value) (kept : numericStore value = value) :
    Value.store .real (realRead value) = realRead value := by
  cases value with
  | integer _ | real _ => simp only [realRead, Value.store, positiveZero_positiveZero]
  | null | blob _ => rfl
  | text _ => simp only [realRead, Value.store, kept]

/-- For every value that is not a REAL, {name}`Value.store` with REAL affinity is
{name}`realRead` of {name}`numericStore`. Proof sketch: by cases on the value; each
non-REAL case is the defining equation, and the REAL case contradicts the premise. -/
theorem Value.store_real_other (value : Value) (other : ∀ bits, value ≠ .real bits) :
    Value.store .real value = realRead (numericStore value) := by
  cases value <;> simp_all [Value.store]

/-- For every affinity and value, {name}`Value.store` applied twice with the affinity equals
{name}`Value.store` applied once: a stored value is in its stored form. Proof sketch: BLOB
and TEXT by cases; NUMERIC and INTEGER by {name}`numericStore_numericStore`; REAL by
{name}`positiveZero_positiveZero` for a REAL value and by {name}`Value.store_real_realRead`
for every other value. -/
theorem Value.store_store (affinity : Affinity) (value : Value) :
    Value.store affinity (Value.store affinity value) = Value.store affinity value := by
  cases affinity with
  | blob => rfl
  | numeric | integer => exact numericStore_numericStore value
  | text => cases value <;> rfl
  | real =>
    cases value with
    | real bits => simp only [Value.store, positiveZero_positiveZero]
    | null => rw [Value.store_real_other .null (by simp)]; exact Value.store_real_realRead _ (numericStore_numericStore _)
    | integer whole =>
      rw [Value.store_real_other (.integer whole) (by simp)]; exact Value.store_real_realRead _ (numericStore_numericStore _)
    | text bytes =>
      rw [Value.store_real_other (.text bytes) (by simp)]; exact Value.store_real_realRead _ (numericStore_numericStore _)
    | blob bytes =>
      rw [Value.store_real_other (.blob bytes) (by simp)]; exact Value.store_real_realRead _ (numericStore_numericStore _)

/-- For every value, {name}`Value.store` with TEXT affinity is not an INTEGER or a REAL. -/
theorem Value.store_text_not_number (value : Value) :
    (∀ whole, Value.store .text value ≠ .integer whole) ∧ (∀ bits, Value.store .text value ≠ .real bits) := by
  cases value <;> simp [Value.store]

/-- For every affinity, {name}`Value.store` keeps NULL. Proof sketch: each affinity's case
returns NULL unchanged by its definition. -/
theorem Value.store_null (affinity : Affinity) : Value.store affinity .null = .null := by
  cases affinity <;> rfl

/-- For all bytes, a TEXT value stored under INTEGER affinity is {name}`numericText` of its
bytes: the number when the text is a number, and the same TEXT otherwise. For example,
{assert}`Value.store .integer (.text [49, 50]) = .integer 12`. Proof sketch: {name}`Value.store`
under INTEGER affinity is {name}`numericStore`, which is {name}`numericText` on TEXT, by
definition. -/
theorem Value.store_integer_text (bytes : List UInt8) : Value.store .integer (.text bytes) = numericText bytes :=
  rfl

end Belay.Sqlite.Model
