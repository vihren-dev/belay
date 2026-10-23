import Belay.Sqlite.Model.StoreValue

set_option doc.verso true

/-! Examples of store-time affinity ({lit}`storeValue`), one per rule of the amendment's
table in ADR 0012, with the neighbors of its "Testing" list. The expected values are
SQLite 3.51.0's stored values for the same writes. -/

namespace Belay.Sqlite.Model.StoreValueExamples

/-- A text value from a string. -/
def text (string : String) : Value := .text string.toUTF8.toList

/-- A REAL value from a double. -/
def real (double : Float) : Value := .real double.toBits

/-- The stored values of one value under INTEGER, NUMERIC, REAL, TEXT and BLOB affinity. -/
def stored (value : Value) : List Value :=
  [.integer, .numeric, .real, .text, .blob].map (storeValue · value)

-- Well-formed number text becomes a number, INTEGER first; a REAL column reads it as REAL.
#guard stored (text "3.0e+5") == [.integer 300000, .integer 300000, real 300000.0, text "3.0e+5", text "3.0e+5"]
#guard stored (text " 12 ") == [.integer 12, .integer 12, real 12.0, text " 12 ", text " 12 "]
-- Hexadecimal and other text stay TEXT.
#guard stored (text "0x10") == [text "0x10", text "0x10", text "0x10", text "0x10", text "0x10"]
#guard stored (text "abc") == [text "abc", text "abc", text "abc", text "abc", text "abc"]
-- Integer text outside 64 bits becomes REAL; an overflowing exponent becomes infinity.
#guard stored (text "9223372036854775808") ==
  [real 9223372036854775808.0, real 9223372036854775808.0, real 9223372036854775808.0,
   text "9223372036854775808", text "9223372036854775808"]
#guard stored (text "1e400") == [.real 0x7FF0000000000000, .real 0x7FF0000000000000, .real 0x7FF0000000000000,
  text "1e400", text "1e400"]
-- A whole REAL becomes INTEGER, except at 2^63; TEXT keeps 15 significant digits.
#guard stored (real 5.0) == [.integer 5, .integer 5, real 5.0, text "5.0", real 5.0]
#guard stored (real 5.5) == [real 5.5, real 5.5, real 5.5, text "5.5", real 5.5]
#guard stored (real 9223372036854775808.0) ==
  [real 9223372036854775808.0, real 9223372036854775808.0, real 9223372036854775808.0,
   text "9.22337203685478e+18", real 9223372036854775808.0]
-- An integer in a REAL column is read back as the nearest double.
#guard stored (.integer 9007199254740993) ==
  [.integer 9007199254740993, .integer 9007199254740993, real 9007199254740992.0,
   text "9007199254740993", .integer 9007199254740993]
-- A REAL column reads -0.0 back as +0.0; NUMERIC and INTEGER store the integer 0, TEXT "0.0".
#guard stored (.real 0x8000000000000000) == [.integer 0, .integer 0, real 0.0, text "0.0", .real 0x8000000000000000]
-- A BLOB and NULL never change.
#guard stored (.blob [49, 50]) == List.replicate 5 (.blob [49, 50])
#guard stored .null == List.replicate 5 .null

end Belay.Sqlite.Model.StoreValueExamples
