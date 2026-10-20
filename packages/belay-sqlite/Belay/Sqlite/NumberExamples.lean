import Belay.Sqlite.NumberConvert
import Belay.Sqlite.RealText
import Belay.Sqlite.Arithmetic
import Belay.Sqlite.Summation
import Belay.Sqlite.Comparison

set_option doc.verso true

/-! Checked examples of SQLite's conversions between text and numbers (ADR 0012, slice 2).
Each expected value is the result of a {lit}`CAST` or an arithmetic operator in the
pinned native SQLite 3.51.0. The examples fix the intended reading of each
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
-- REAL to text: 15 significant digits, plain notation for exponents from -4 to 14,
-- at least one digit after the point, and Inf for an infinity.
#guard [realText 0, realText (-0.0), realText 1, realText 0.1, realText 1e14, realText 1e15] ==
  (["0.0", "0.0", "1.0", "0.1", "100000000000000.0", "1.0e+15"]).map (·.toUTF8.toList)
#guard [realText 123456789012345.6, realText 0.0001, realText 0.00001, realText (1 / 3), realText (-2.5)] ==
  (["123456789012346.0", "0.0001", "1.0e-05", "0.333333333333333", "-2.5"]).map (·.toUTF8.toList)
#guard [realText 1.7976931348623157e308, realText 5e-324, realText (Float.ofBits 0x7FF0000000000000),
  realText (Float.ofBits 0xFFF0000000000000)] ==
  (["1.79769313486232e+308", "4.94065645841247e-324", "Inf", "-Inf"]).map (·.toUTF8.toList)
-- Integer arithmetic is exact while it fits; an overflow gives a REAL.
#guard ArithmeticOperator.add.apply (.integer 7) (.integer (-3)) == .integer 4
#guard ArithmeticOperator.add.apply (.integer int64Maximum) (.integer 1) == .real 0x43E0000000000000
#guard ArithmeticOperator.divide.apply (.integer int64Minimum) (.integer (-1)) == .real 0x43E0000000000000
-- Integer division truncates toward zero; the remainder has the sign of the dividend.
#guard [ArithmeticOperator.divide.apply (.integer (-7)) (.integer 2), ArithmeticOperator.remainder.apply (.integer (-7)) (.integer 2)] ==
  [.integer (-3), .integer (-1)]
-- Division and remainder by zero, NULL operands and a NaN result are NULL.
#guard [ArithmeticOperator.divide.apply (.integer 1) (.integer 0), ArithmeticOperator.remainder.apply (.real 0x3FF8000000000000) (.integer 0),
  ArithmeticOperator.add.apply .null (.integer 1),
  ArithmeticOperator.subtract.apply (.real 0x7FF0000000000000) (.real 0x7FF0000000000000)] == [.null, .null, .null, .null]
-- A REAL remainder converts both operands to integers: 7.5 % 2 is 1.0.
#guard ArithmeticOperator.remainder.apply (.real 0x401E000000000000) (.integer 2) == .real 0x3FF0000000000000
-- TEXT operands convert: ' 7 ' is the integer 7, '1.5' is a REAL, 'abc' is 0.
#guard [ArithmeticOperator.add.apply (.text " 7 ".toUTF8.toList) (.integer 1), ArithmeticOperator.multiply.apply (.text "1.5".toUTF8.toList) (.integer 2),
  ArithmeticOperator.add.apply (.text "abc".toUTF8.toList) (.integer 1)] == [.integer 8, .real 0x4008000000000000, .integer 1]
-- CAST: NUMERIC makes an integer of '4.0', INTEGER truncates a REAL, TEXT renders a REAL.
#guard [castValue .numeric (.text "4.0".toUTF8.toList), castValue .integer (.real 0xC004000000000000),
  castValue .text (.real 0x3FB999999999999A), castValue .blob (.integer 12)] ==
  [.integer 4, .integer (-2), .text "0.1".toUTF8.toList, .blob "12".toUTF8.toList]
-- SUM is exact over integers; an overflow fails unless a later REAL input follows;
-- TEXT gets numeric affinity, and text that is not a number adds 0.0.
#guard (sumOf [.integer int64Maximum, .integer 1]).sumValue == none
#guard (sumOf [.integer int64Maximum, .integer 1, .real 0x3FE0000000000000]).sumValue == some (.real 4890909195324358656)
#guard [(sumOf []).sumValue, (sumOf [.null]).sumValue, (sumOf [.text "7".toUTF8.toList, .integer 1]).sumValue,
  (sumOf [.text "abc".toUTF8.toList]).sumValue] == [some .null, some .null, some (.integer 8), some (.real 0)]
-- AVG never fails: the overflowing sum continues in doubles.
#guard [(sumOf []).averageValue, (sumOf [.integer int64Maximum, .integer 1]).averageValue] ==
  [.null, .real 4886405595696988160]

-- A NaN double is NULL as a value (realValue), as SQLite stores it. The model never creates a
-- NaN REAL; one written by hand is not NULL: only NULL is, and `x IS NULL` is false for it.
#guard realValue (0.0 / 0.0) == .null
#guard !(Value.real 0x7FF8000000000000).isNull && (Value.null).isNull
#guard Comparison.apply .is (.real 0x7FF8000000000000) .null == .integer 0

end Belay.Sqlite.NumberExamples
