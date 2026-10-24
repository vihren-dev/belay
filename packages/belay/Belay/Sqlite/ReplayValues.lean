import Belay.Sqlite.Values

set_option doc.verso true

/-! SQL spellings for replay values. Text is encoded through a hexadecimal BLOB cast so
quotes, NULs and arbitrary bytes survive without changing the value's storage class. -/

namespace Belay.Sqlite.Replay

open Belay.Sqlite.Model

/-- Decode the ASCII output of the model's numeric and hexadecimal formatters. -/
private def ascii (bytes : List UInt8) : String :=
  String.ofList (bytes.map fun byte => Char.ofNat byte.toNat)

/-- A BLOB literal preserving every byte, including an empty BLOB. -/
def blobLiteral (bytes : List UInt8) : String :=
  "X'" ++ ascii (Resolved.hexValue (.blob bytes)).textBytes ++ "'"

/-- An SQL value expression that preserves the supplied storage class and bytes. Text uses
CAST from a BLOB to preserve NULs. Out-of-range integers and NaN have no native SQLite value
and return none. REAL spelling reuses the model's formatter and checks its parsed bits;
a spelling that loses signed zero is refused. Construction validation checks stored values. -/
def valueLiteral : Value → Option String
  | .null => some "NULL"
  | .integer value => if fitsInt64Range value then some (toString value) else none
  | .real bits =>
    if (Float.ofBits bits).isNaN then none else
      let text := ascii (Resolved.quoteReal (Float.ofBits bits))
      if (literalDefault (.numeric text)).toOption == some (.real bits) then some text else none
  | .text bytes => some ("CAST(" ++ blobLiteral bytes ++ " AS TEXT)")
  | .blob bytes => some (blobLiteral bytes)

/-- A quoted SQL identifier whose UTF-8 bytes round-trip unchanged. Names that cannot be
represented by Lean's UTF-8 strings return none rather than silently replacing bytes. -/
def identifier (name : Identifier) : Option String :=
  if name.text.toUTF8.toList != name.bytes then none
  else some ("\"" ++ name.text.replace "\"" "\"\"" ++ "\"")

end Belay.Sqlite.Replay
