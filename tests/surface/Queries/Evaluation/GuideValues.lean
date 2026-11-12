import Belay

/-! A fixture of `tests/surface_guide_test.py`: the examples of the user guide's section
"Values", as the guide writes them, over the surface's names (`Belay/Sqlite/Values.lean`). The
file fails to elaborate when an example does not hold. -/

open Belay.Sqlite

-- Literals coerce: an integer, a string and a decimal.
example : (10 : Value) = .integer 10 := rfl
example : ("acme" : Value) = .text [97, 99, 109, 101] := by decide +kernel
example : (2.5 : Value) = .real (2.5 : Float).toBits := rfl

-- NULL comes first, then numbers, then text, then blobs.
example : Value.compare .null 1 = .lt := by decide
example : Value.compare 1 "a" = .lt := by decide +kernel
example : Value.compare "a" (.blob []) = .lt := by decide +kernel

-- Three-valued truth; a WHERE keeps a row only for Truth.true.
example : Value.null.truth = .unknown := by decide
example : (0 : Value).truth = .false := by decide
example : ((1 : Value).and .null).truth = .unknown := by decide

-- `Value.store .integer "12"` is `12`.
example : Value.store .integer "12" = 12 := by decide +kernel

-- The lemmas of the section, in the `Value` namespace.
example (a b : Value) : (a.and b).truth = a.truth.and b.truth := Value.truth_and a b
example (value : Value) (ranked : value.rank ≠ 0) : Value.compare .null value = .lt :=
  Value.compare_null value ranked
example (bytes : List UInt8) : Value.store .integer (.text bytes) = Belay.Sqlite.Model.numericText bytes :=
  Value.store_integer_text bytes
