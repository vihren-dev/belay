import Belay.Sqlite.Functions.Printf

set_option doc.verso true

/-! Checked examples of {lit}`printf` and {lit}`format` (ADR 0015, slice 6). Each result was
checked on native SQLite 3.51.0, one statement per line; a generated set of 951 formats over
values of each type agreed with native SQLite as well. -/

namespace Belay.Sqlite.Resolved.PrintfExamples

open Belay.Sqlite

/-- The TEXT value of a string. -/
def text (string : String) : Value := .text string.toUTF8.toList

/-- Whether {lit}`printf` of a format and arguments gives the text. -/
def gives (format : String) (arguments : List Value) (expected : String) : Bool :=
  match printfValue (text format :: arguments) with
  | .ok value => value == text expected
  | .error _ => false

-- Integers: width, the - and 0 flags, the sign flags, commas, bases and the # prefix.
#guard gives "%5d|%-5d|%05d|%+d|% d" [.integer 42, .integer 42, .integer (-42), .integer 42, .integer 42]
  "   42|42   |-0042|+42| 42"
#guard gives "%,d|%u|%x|%#X|%#o|%p" [.integer 1234567, .integer (-1), .integer 255, .integer 255, .integer 8, .integer 255]
  "1,234,567|18446744073709551615|ff|0XFF|010|FF"
#guard gives "%r %r %r %r %r" [.integer 1, .integer 2, .integer 3, .integer 11, .integer 112] "1st 2nd 3rd 11th 112th"
-- Doubles: the default precision 6, %g without trailing zeros, the ! flag, NaN and infinities.
#guard gives "%f|%.2f|%e|%g|%g|%!g" [.real (3.14159 : Float).toBits, .real (2.675 : Float).toBits,
  .real (12345.678 : Float).toBits, .real (100000.0 : Float).toBits, .real (1000000.0 : Float).toBits,
  .real (5.0 : Float).toBits] "3.141590|2.67|1.234568e+04|100000|1e+06|5.0"
#guard gives "%f|%+f|%05f" [.real (1.0 / 0.0 : Float).toBits, .real (1.0 / 0.0 : Float).toBits,
  .real (-0.0 : Float).toBits] "Inf|+Inf|0.000000"
-- Text: precision in bytes (two for é) or characters, quoting, and %c repeated.
#guard gives "%.2s|%!.2s|%q|%Q|%Q|%w" [text "été", text "été", text "it's", text "x", .null, text "a\"b"]
  "é|ét|it''s|'x'|NULL|a\"\"b"
#guard gives "%.3c|%5.3c|" [text "ab", text "a"] "aaa|  aaa|"
-- *: an argument as width or precision; a negative width pads on the right; missing
-- arguments are 0 or empty; an unknown conversion ends the output.
#guard gives "%*d|%-*d|%.*f" [.integer 6, .integer 42, .integer (-6), .integer 42, .integer 2, .real (3.14159 : Float).toBits]
  "    42|42    |3.14"
#guard gives "%d %d %s|100%%|a%yb" [] "0 0 |100%|a"
#guard match printfValue [] with
  | .ok value => value == .null
  | .error _ => false

example : gives "%05.1f|%-4s|%x" [.real (-2.25 : Float).toBits, text "ab", .integer 3054] "-02.3|ab  |bee" = true := by
  decide +kernel

end Belay.Sqlite.Resolved.PrintfExamples
