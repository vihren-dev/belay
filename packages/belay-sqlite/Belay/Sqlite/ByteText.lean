set_option doc.verso true

/-! Text as bytes (ADR 0013, step 8): the ASCII case folding and NUL termination that the
SQLite readers of JSON, dates and identifiers share, and a literal for fixed byte texts.
SQLite's text may be invalid UTF-8, so the model compares bytes. -/

namespace Belay.Sqlite

/-- The ASCII lowercase of a byte ({lit}`sqlite3UpperToLower`); every other byte stays
the same. -/
def lowerAscii (byte : UInt8) : UInt8 := if 65 ≤ byte && byte ≤ 90 then byte + 32 else byte

/-- The bytes before the first NUL: what SQLite reads from a value as a C string
({lit}`sqlite3_value_text`). Without a NUL, every byte. -/
def bytesBeforeNul (bytes : List UInt8) : List UInt8 := bytes.takeWhile (· != 0)

/-- Whether the bytes equal a keyword without ASCII case ({lit}`sqlite3StrICmp`). The
keyword is given in lowercase. -/
def equalsKeyword (bytes keyword : List UInt8) : Bool := bytes.map lowerAscii == keyword

/-- A fixed text as its UTF-8 bytes, written {lit}`bytes! "auto"` for the list
{lit}`[97, 117, 116, 111]`. The macro writes the byte list itself, so the kernel and
{lit}`decide` see a literal list and evaluate no string function. -/
macro "bytes! " text:str : term => do
  let items ← text.getString.toUTF8.toList.mapM fun byte => `(($(Lean.quote byte.toNat) : UInt8))
  `(([$(items.toArray),*] : List UInt8))

end Belay.Sqlite
