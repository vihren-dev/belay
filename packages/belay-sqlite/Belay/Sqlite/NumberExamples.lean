import Belay.Sqlite.NumberConvert

set_option doc.verso true

/-! Checked examples of SQLite's text-to-number conversions (ADR 0012, slice 2). Each
expected value is the result of {lit}`CAST(text AS REAL)` or {lit}`CAST(text AS INTEGER)`
in the pinned native SQLite 3.51.0. The examples fix the intended reading of each
rule; the conformance cases compare the conversions with native SQLite. -/

namespace Belay.Sqlite.NumberExamples

open Belay.Sqlite

/-- The IEEE bits of {lit}`sqlite3AtoF` on a string. -/
def realBits (text : String) : UInt64 := (atof text.toUTF8.toList).1.toBits

/-- The value of {lit}`sqlite3Atoi64` on a string. -/
def integerOf (text : String) : Int := (atoi64 text.toUTF8.toList).1

-- Spaces, signs, a fraction without digits before the point, and an exponent.
#guard [realBits "1.5", realBits " 7 ", realBits "+.5", realBits "1e3", realBits "-0"] ==
  [0x3FF8000000000000, 0x401C000000000000, 0x3FE0000000000000, 0x408F400000000000, 0x8000000000000000]
-- Text that is not a number, or only a prefix of one, converts its prefix or to zero.
#guard [realBits "abc", realBits "", realBits ".", realBits "12abc"] == [0, 0, 0, 0x4028000000000000]
-- Overflow to infinity, and the smallest subnormal.
#guard [realBits "1e309", realBits "-1e400", realBits "4.9e-324"] ==
  [0x7FF0000000000000, 0xFFF0000000000000, 1]
-- SQLite's double-double scaling is not correctly rounded: the nearest double of
-- 2.2250738585072011e-308 is 0x000FFFFFFFFFFFFF, and SQLite gives the one above.
#guard realBits "2.2250738585072011e-308" == 0x0010000000000000
#guard realBits "2.6018159083016613186e-270" == 573643863846108179
-- The integer prefix: an exponent or a fraction ends it, and large values saturate.
#guard [integerOf "1e3", integerOf "  -12  ", integerOf "5.", integerOf "0x10", integerOf "abc"] == [1, -12, 5, 0, 0]
#guard [integerOf "9223372036854775808", integerOf "-9223372036854775809", integerOf "99999999999999999999999"] ==
  [9223372036854775807, -9223372036854775808, 9223372036854775807]
-- The result codes: a whole number, a prefix, no digits, too large, and exactly 2^63.
#guard [(atoi64 "7".toUTF8.toList).2, (atoi64 "7x".toUTF8.toList).2, (atoi64 "x".toUTF8.toList).2,
  (atoi64 "99999999999999999999".toUTF8.toList).2, (atoi64 "9223372036854775808".toUTF8.toList).2] == [0, 1, -1, 2, 3]
#guard [(atof "1.5".toUTF8.toList).2, (atof "15".toUTF8.toList).2, (atof "1e5".toUTF8.toList).2,
  (atof "1.5x".toUTF8.toList).2, (atof "x".toUTF8.toList).2] == [2, 1, 2, -1, 0]
-- REAL to INTEGER saturates and truncates toward zero.
#guard [realToI64 1e19, realToI64 (-1e19), realToI64 (-2.7), realToI64 2.7] ==
  [9223372036854775807, -9223372036854775808, -2, 2]

end Belay.Sqlite.NumberExamples
