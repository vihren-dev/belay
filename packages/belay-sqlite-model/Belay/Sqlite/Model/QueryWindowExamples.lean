import Belay.Sqlite.Model.QueryWindow

set_option doc.verso true

/-! Examples of the values of {lit}`LIMIT ?` and {lit}`OFFSET ?` (ADR 0019, slice 1), with the values
of native SQLite 3.51.0: {lit}`windowInteger` reads each kind of value as {lit}`OP_MustBeInt` does.
The kernel checks each example ({lit}`decide +kernel`). The acceptance fixture
{lit}`SelectParameterWindowCases` checks how a query reads its window. -/

namespace Belay.Sqlite.Model.QueryWindowExamples

open Resolved

/-- A text value from a string. -/
def text (string : String) : Value := .text string.toUTF8.toList

-- An integer, a whole REAL (2.0, whose bits are 0x4000000000000000) and text that numeric
-- affinity makes a whole number give the integer: '2', ' 2 ', '+2', '2.0' and '1e1'.
example : [windowInteger (.integer 2), windowInteger (.real 0x4000000000000000), windowInteger (text "2"),
    windowInteger (text " 2 "), windowInteger (text "+2"), windowInteger (text "2.0"), windowInteger (text "1e1")] =
    [some 2, some 2, some 2, some 2, some 2, some 2, some 10] := by decide +kernel
-- NULL, a blob, '', 'abc' and '0x10' have no integer.
example : [windowInteger .null, windowInteger (.blob [2]), windowInteger (text ""), windowInteger (text "abc"),
    windowInteger (text "0x10")] = [none, none, none, none, none] := by decide +kernel
-- 2.5 (bits 0x4004000000000000), '2.5', 1e20 (bits 0x4415AF1D78B58C40) and integer text
-- outside 64 bits have no integer.
example : [windowInteger (.real 0x4004000000000000), windowInteger (text "2.5"), windowInteger (.real 0x4415AF1D78B58C40),
    windowInteger (text "9223372036854775808")] = [none, none, none, none] := by decide +kernel

end Belay.Sqlite.Model.QueryWindowExamples
