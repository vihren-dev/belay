import Belay.Sqlite.Model.Functions.Scalar

set_option doc.verso true

/-! Examples of the scalar functions of ADR 0015, slice 1, checked by {lit}`#guard` when the
package builds, and by the kernel where the authored corpus needs it. Each value was checked
with native SQLite 3.51.0. -/

namespace Belay.Sqlite.Model.Resolved.FunctionExamples

open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- The UTF-8 bytes of a string. -/
def text (value : String) : Value := .text value.toUTF8.toList

/-- The value of a function over argument values, NULL when it fails. -/
def value (function : ScalarFunction) (arguments : List Value) : Value :=
  match function.apply arguments with
  | .ok result => result
  | .error _ => .null

/-- Whether the function fails over the argument values. -/
def fails (function : ScalarFunction) (arguments : List Value) : Bool :=
  match function.apply arguments with
  | .ok _ => false
  | .error _ => true

-- typeof, length and octet_length: characters of text before a NUL, bytes otherwise.
#guard value .typeof [.real (1.5 : Float).toBits] == text "real"
#guard value .length [text "héllo"] == .integer 5
#guard value .length [.text [97, 0, 98]] == .integer 1
#guard value .length [.blob [1, 2]] == .integer 2
#guard value .length [.real (12.5 : Float).toBits] == .integer 4
#guard value .octetLength [text "é"] == .integer 2
#guard value .length [.null] == .null
-- abs: text and BLOB as a REAL; the smallest integer fails.
#guard value .abs [text "-3"] == .real (3.0 : Float).toBits
#guard value .abs [text "x"] == .real (0.0 : Float).toBits
#guard value .abs [.integer (-7)] == .integer 7
#guard fails .abs [.integer (-(2 ^ 63))]
-- sign: numbers and text that reads as a number.
#guard value .sign [text "-2.5"] == .integer (-1)
#guard value .sign [text "x"] == .null
#guard value .sign [.blob [49]] == .null
-- zeroblob: none for a negative size.
#guard value .zeroblob [.integer (-1)] == .blob []
#guard value .zeroblob [.integer 3] == .blob [0, 0, 0]
-- nullif, min and max under a collation; min takes the later argument on a tie.
#guard value (.nullif .nocase) [text "A", text "a"] == .null
#guard value (.min .binary) [.integer 1, text "a", .null] == .null
#guard value (.max .binary) [.integer 1, .real (2.5 : Float).toBits] == .real (2.5 : Float).toBits
#guard value (.min .nocase) [text "B", text "a"] == text "a"
#guard value (.min .nocase) [text "a", text "A"] == text "A"
#guard value (.max .nocase) [text "a", text "A"] == text "a"
-- LIKE ignores ASCII case only; GLOB has classes with ^ for a negated class.
#guard value .like [text "a%", text "ABC"] == .integer 1
#guard value .like [text "àb", text "Àb"] == .integer 0
#guard value .like [text "_", text "é"] == .integer 1
#guard value .like [text "a\\_c", text "a_c", text "\\"] == .integer 1
#guard value .like [text "a\\_c", text "abc", text "\\"] == .integer 0
#guard value .like [text "a%", .integer 12] == .integer 0
#guard value .like [text "1%", .integer 12] == .integer 1
#guard value .like [text "a", .null] == .null
#guard fails .like [text "a", text "a", text "xy"]
#guard value .like [text "a", text "a", .null] == .null
#guard value .glob [text "A*", text "abc"] == .integer 0
#guard value .glob [text "a[b-c]?", text "abc"] == .integer 1
#guard value .glob [text "[^a]", text "x"] == .integer 1
#guard value .glob [text "[!a]", text "x"] == .integer 0
#guard value .glob [text "*[c]", text "abc"] == .integer 1
#guard value .glob [text "*b*", text "abc"] == .integer 1

-- The text functions, as SQLite's func.c computes them.
#guard value .substr [text "héllo", .integer 2, .integer 2] == text "él"
#guard value .substr [text "abc", .integer 0, .integer 2] == text "a"
#guard value .substr [text "abc", .integer (-2)] == text "bc"
#guard value .instr [text "héllo", text "l"] == .integer 3
#guard value .replace [text "aaa", text "aa", text "b"] == text "ba"
#guard value (.trim .both) [text "xxaxx", text "x"] == text "a"
#guard value .hex [text "é"] == text "C3A9"
#guard value .unhex [text "0a-ff", text "-"] == .blob [10, 255]
#guard value .char [.integer 72, .integer 233] == text "Hé"
#guard value .unicode [text "é"] == .integer 233
#guard value .quote [.real (1.0 / 3.0 : Float).toBits] == text "3.333333333333333148e-01"
#guard value .concatWs [text "-", text "a", .null, text "b"] == text "a-b"
#guard fails .unistr [text "a\\xb"]

-- The numeric functions (slice 2): exact roundings, the sign of zero, fmod and the constants.
#guard value .round [.real (2.5 : Float).toBits] == .real (3.0 : Float).toBits
#guard value .round [.real (-2.5 : Float).toBits] == .real (-3.0 : Float).toBits
#guard value .round [.real (1.005 : Float).toBits, .integer 2] == .real (1.0 : Float).toBits
#guard value .round [.real (2.5 : Float).toBits, .null] == .null
#guard value .floor [.real (-2.5 : Float).toBits] == .real (-3.0 : Float).toBits
#guard value .floor [.integer 3] == .integer 3
#guard value .floor [text "x"] == .null
#guard value .ceil [.real (2.1 : Float).toBits] == .real (3.0 : Float).toBits
#guard value .trunc [.real (-2.7 : Float).toBits] == .real (-2.0 : Float).toBits
#guard value .trunc [.real (-0.5 : Float).toBits] == .real (-(0.0 : Float)).toBits
#guard value .sqrt [.integer (-1)] == .null
#guard value .mod [.real (7.5 : Float).toBits, .integer 2] == .real (1.5 : Float).toBits
#guard value .mod [.integer (-7), .integer 3] == .real (-1.0 : Float).toBits
#guard value .mod [.integer 1, .integer 0] == .null
#guard value .degrees [.real piDouble.toBits] == .real (180.0 : Float).toBits

-- The kernel reduces pattern matching, which the proofs of the authored cases need.
example : value .like [text "%b_", text "aBc"] = .integer 1 := by decide +kernel
example : value .mod [.real (1e300 : Float).toBits, .integer 7] = value .mod [.real (1e300 : Float).toBits, .integer 7] := by
  decide +kernel

end Belay.Sqlite.Model.Resolved.FunctionExamples
