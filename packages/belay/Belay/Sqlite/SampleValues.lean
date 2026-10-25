import Plausible.Arbitrary
import Plausible.Shrinkable
import Belay.Sqlite.Values

set_option doc.verso true

/-! The value generator shared by Plausible and SQL counterexample search. Stable SQL
boundaries make small samples useful; shrinking only proposes replacements for certification. -/

namespace Belay.Sqlite.Sampling

open Plausible

/-- Candidate values for SQL boundaries, in stable order: NULL, small integers, the signed
64-bit limits, half the SUM overflow boundary, ASCII and non-ASCII case pairs, quoted text,
BLOBs and an ordinary REAL. These are examples, not a complete value domain.
The value generator can also include a claim's own constants. -/
def boundaryValues : List Value :=
  [.null, .integer 0, .integer 1, .integer (-1),
   .integer (-9223372036854775808), .integer 9223372036854775807,
   .integer 4611686018427387904,
   .text [], .text "a".toUTF8.toList, .text "A".toUTF8.toList,
   .text "æ".toUTF8.toList, .text "Æ".toUTF8.toList,
   .text "a'b".toUTF8.toList, .blob [], .blob [0, 39, 255], .real 0x3ff8000000000000]

/-- Select a value from the supplied constants followed by {name}`boundaryValues`.
Use no constants for the default SQL boundary distribution. -/
def value (constants : List Value := []) : Gen Value :=
  Gen.elements (constants ++ boundaryValues) (by simp [boundaryValues])

/-- Suggest smaller values: NULL first, then smaller integers or shorter byte strings.
A NULL has no shrink; a REAL shrinks to NULL or INTEGER zero. The checker must certify
that any selected replacement still refutes its original claim. -/
def shrinkValue : Value → List Value
  | .null => []
  | .integer number => .null :: (Shrinkable.shrink number).map Value.integer
  | .real _ => [.null, .integer 0]
  | .text bytes => .null :: (Shrinkable.shrink bytes).map Value.text
  | .blob bytes => .null :: (Shrinkable.shrink bytes).map Value.blob

/-- Run a Plausible generator with an explicit seed and size, without shared random state.
The same generator, seed and size have the same result. For example, use seed zero and
size two for a small repeatable SQL search. A generator failure remains an error. -/
def seeded (generator : Gen α) (seed : Nat := 0) (size : Nat := 2) : Except GenError α :=
  (Plausible.runRandWith seed generator).run ⟨size⟩

end Belay.Sqlite.Sampling

namespace Belay.Sqlite

/-- Plausible uses the same SQL boundary generator as the checker. -/
instance : Plausible.Arbitrary Value := ⟨Sampling.value⟩

/-- Plausible uses the same value shrink proposals as the checker. -/
instance : Plausible.Shrinkable Value := ⟨Sampling.shrinkValue⟩

end Belay.Sqlite
