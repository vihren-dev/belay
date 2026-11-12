import Belay.Sqlite.Model.Queries.Select.Defaults
import Belay.Sqlite.Model.Schema.Columns.Defaults
import Belay.Sqlite.Queries.Evaluation.Values

set_option doc.verso true

/-! SQL spellings for replay values. Text that a string literal keeps in the shell is a string literal,
for example {lit}`'a'`; other text is encoded through a hexadecimal BLOB cast, so NULs and
arbitrary bytes survive without changing the value's storage class. -/

namespace Belay.Sqlite.Replay

open Belay.Sqlite.Model

/-- Decode the ASCII output of the model's numeric and hexadecimal formatters. -/
private def ascii (bytes : List UInt8) : String :=
  String.ofList (bytes.map fun byte => Char.ofNat byte.toNat)

/-- A BLOB literal preserving every byte, including an empty BLOB. -/
def blobLiteral (bytes : List UInt8) : String :=
  "X'" ++ ascii (Resolved.hexValue (.blob bytes)).textBytes ++ "'"

/-- The SQL string literal of a text, for example {lit}`'a''b'` for the text {lit}`a'b`: the
text's characters with each quote doubled. It is none when the bytes are not UTF-8, hold a
NUL byte, which a literal cannot hold, or hold a carriage return: the {lit}`sqlite3` shell reads a
script by lines and gives a CR LF inside a literal as LF alone. -/
def textLiteral (bytes : List UInt8) : Option String := do
  guard (!bytes.contains 0 && !bytes.contains 13)
  let text ← String.fromUTF8? ⟨bytes.toArray⟩
  return "'" ++ text.replace "'" "''" ++ "'"

/-- An SQL value expression that preserves the supplied storage class and bytes. Text is its
string literal ({name}`textLiteral`) when it has one, and otherwise a CAST from a BLOB.
Out-of-range integers and NaN have no native SQLite value
and return none. REAL spelling reuses the model's formatter and checks its parsed bits;
a spelling that loses signed zero is refused. Construction validation checks stored values. -/
def valueLiteral : Value → Option String
  | .null => some "NULL"
  | .integer value => if fitsInt64Range value then some (toString value) else none
  | .real bits =>
    if (Float.ofBits bits).isNaN then none else
      let text := ascii (Resolved.quoteReal (Float.ofBits bits))
      if (literalDefault (.numeric text)).toOption == some (.real bits) then some text else none
  | .text bytes => some ((textLiteral bytes).getD ("CAST(" ++ blobLiteral bytes ++ " AS TEXT)"))
  | .blob bytes => some (blobLiteral bytes)

/-- A quoted SQL identifier whose UTF-8 bytes round-trip unchanged. Names that cannot be
represented by Lean's UTF-8 strings return none rather than silently replacing bytes. -/
def identifier (name : Identifier) : Option String :=
  if name.text.toUTF8.toList != name.bytes then none
  else some ("\"" ++ name.text.replace "\"" "\"\"" ++ "\"")

end Belay.Sqlite.Replay
