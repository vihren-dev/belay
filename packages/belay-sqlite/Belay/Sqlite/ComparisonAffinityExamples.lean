import Belay.Sqlite.ExprEval

set_option doc.verso true

/-! Checked examples of comparison affinity and of values as conditions (ADR 0013, D4).
Each value was checked on native SQLite 3.51.0, one statement per line. -/

namespace Belay.Sqlite.Resolved.ComparisonAffinityExamples

/-- The text value of a string. -/
def text (value : String) : Value := .text value.toUTF8.toList

/-- The value of {lit}`left = right` under the affinity. -/
def equals (affinity : Option Affinity) (left right : Value) : Value :=
  (Expr.compare .eq affinity (.literal left) (.literal right)).eval (.plain 0) []

-- An INTEGER column against '1' compares the number: `intcol = '1'` is 1.
#guard equals (some .integer) (.integer 1) (text "1") == .integer 1
-- NUMERIC affinity converts only text that looks like a number.
#guard equals (some .numeric) (.integer 1) (text "1x") == .integer 0
-- An untyped (BLOB) column against 1, and two literals, compare the values as they are.
#guard equals (some .blob) (text "1") (.integer 1) == .integer 0
#guard equals none (text "1") (.integer 1) == .integer 0
-- A TEXT column against 1 compares the text: `textcol = 1` is 1 when the column holds '1'.
#guard equals (some .text) (text "1") (.integer 1) == .integer 1
-- `CAST(1 AS TEXT) = 1` has TEXT affinity from the CAST, so it is 1.
#guard (Expr.compare .eq (some .text) (.cast .text (.literal (.integer 1))) (.literal (.integer 1))).eval (.plain 0) [] ==
  .integer 1
-- An integer never goes through a double: 2^53 + 1 against the REAL 2^53 is not equal.
#guard equals (some .numeric) (.real (9007199254740992.0 : Float).toBits) (.integer 9007199254740993) == .integer 0

-- A value is a condition by its numeric prefix (sqlite3VdbeBooleanValue).
#guard truthy (text "1ab") && !truthy (text "abc") && truthy (text "0.9") && !truthy (text "0.0")
#guard truthy (.real (0.9 : Float).toBits) && truthy (.blob [49]) && !truthy .null

end Belay.Sqlite.Resolved.ComparisonAffinityExamples
