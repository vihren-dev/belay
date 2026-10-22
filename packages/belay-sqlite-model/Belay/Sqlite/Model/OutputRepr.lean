import Belay.Sqlite.Model.Output

set_option doc.verso true

/-! How {lit}`#eval` shows an {name}`Belay.Sqlite.Model.Output`: as a user writes it, with each
value as the literal that gives it. For example, the outputs of an UPDATE that changes one row
and of a query with one row show as {lit}`[done 1, rows [[1, 10]]]`. -/

namespace Belay.Sqlite.Model

/-- The bytes as hexadecimal digits, two for each byte. For example,
{assert}`hexBytes [10, 255] = "0aff"`. -/
def hexBytes (bytes : List UInt8) : String :=
  String.join (bytes.map fun byte =>
    let digits := Nat.toDigits 16 byte.toNat
    String.ofList (if digits.length < 2 then '0' :: digits else digits))

/-- The value as the literal that gives it: an integer as its digits, a text as a Lean string
literal, a REAL as its decimal, NULL as {lit}`null`, and a BLOB as {lit}`x'...'`, as in SQL. A
text whose bytes are not UTF-8 shows its bytes as {lit}`text x'...'`. For example, the value
{lean}`Value.text "acme".toUTF8.toList` shows as {lit}`"acme"`. -/
def Value.display : Value → Std.Format
  | .null => "null"
  | .integer value => repr value
  | .real bits => toString (Float.ofBits bits)
  | .text bytes => match String.fromUTF8? ⟨bytes.toArray⟩ with
    | some decoded => repr decoded
    | none => s!"text x'{hexBytes bytes}'"
  | .blob bytes => s!"x'{hexBytes bytes}'"

/-- The rows of a result as a list of lists of values ({name}`Value.display`). -/
def displayRows (rows : List (List Value)) : Std.Format :=
  Std.Format.bracket "[" (.joinSep (rows.map fun row => Std.Format.bracket "[" (.joinSep (row.map Value.display) ("," ++ .line)) "]")
    ("," ++ .line)) "]"

/-- An output as the constructor name and its argument, without the namespace: for example
{lit}`done 1`, {lit}`rows [[1, 10]]`, {lit}`error 19`, {lit}`oneOf [[["ada"]], [["bob"]]]` and
{lit}`unmodeled "..."`. -/
instance : Repr Output where
  reprPrec output _ := match output with
    | .rows rows => "rows " ++ displayRows rows
    | .done changes => "done " ++ repr changes
    | .error code => "error " ++ repr code
    | .oneOf results => "oneOf " ++ Std.Format.bracket "[" (.joinSep (results.map displayRows) ("," ++ .line)) "]"
    | .unmodeled reason => "unmodeled " ++ repr reason

end Belay.Sqlite.Model
