set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The ASCII lowercase of a byte ({lit}`sqlite3UpperToLower`); every other byte stays
the same. -/
def lowerAscii (byte : UInt8) : UInt8 := if 65 ≤ byte && byte ≤ 90 then byte + 32 else byte

/-- Whether the bytes equal a keyword without ASCII case ({lit}`sqlite3StrICmp`). The
keyword is given in lowercase. -/
def equalsKeyword (bytes keyword : List UInt8) : Bool := bytes.map lowerAscii == keyword

/-- A fixed text as its UTF-8 bytes, written {lit}`bytes! "auto"` for the list
{lit}`[97, 117, 116, 111]`. The macro writes the byte list itself, so the kernel and
{lit}`decide` see a literal list and evaluate no string function. -/
macro "bytes! " text:str : term => do
  let items ← text.getString.toUTF8.toList.mapM fun byte => `(($(Lean.quote byte.toNat) : UInt8))
  `(([$(items.toArray),*] : List UInt8))

end Belay.Sqlite.Model
