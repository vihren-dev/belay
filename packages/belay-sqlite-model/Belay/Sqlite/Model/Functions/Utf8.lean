import Belay.Sqlite.Model.Declarations

set_option doc.verso true

/-! SQLite 3.51.0's reading and writing of UTF-8 text in its functions ({lit}`sqlite3Utf8Read`,
{lit}`SQLITE_SKIP_UTF8`, {lit}`sqlite3AppendOneUtf8Character`), over byte lists that the
kernel reduces. The text of a function argument is a C string, so these functions see the
bytes before the first NUL ({lit}`bytesBeforeNul`). -/

namespace Belay.Sqlite.Model.Resolved

/-- The value bits of a lead byte of {lit}`0xC0` or more ({lit}`sqlite3Utf8Trans1`): the bits after
the length prefix of a two-, three- or four-byte form, and zero for the longer forms that
UTF-8 does not have. -/
def utf8LeadBits (byte : UInt8) : UInt32 :=
  let index := byte.toNat - 0xC0
  (if index < 32 then index else if index < 48 then index - 32 else if index < 56 then index - 48
    else if index < 60 then index - 56 else if index < 62 then index - 60 else 0).toUInt32

/-- The continuation bytes ({lit}`0x80` to {lit}`0xBF`) at the start of the bytes folded into a
code point, and the bytes after them. The shift wraps at 32 bits, as in SQLite. -/
def utf8Continue (code : UInt32) : List UInt8 → UInt32 × List UInt8
  | byte :: rest => if byte &&& 0xC0 == 0x80 then utf8Continue ((code <<< 6) + (byte &&& 0x3F).toUInt32) rest
    else (code, byte :: rest)
  | [] => (code, [])

/-- The next character of a C string and the bytes after it ({lit}`sqlite3Utf8Read`): 0 at the
end; an ASCII byte as it is; a lead byte with its continuation bytes, and {lit}`U+FFFD` for an
overlong form, a surrogate, {lit}`U+FFFE` and {lit}`U+FFFF`. For example,
{lean}`(utf8Read [0xC3, 0xA9]).1 = 0xE9`. -/
def utf8Read : List UInt8 → UInt32 × List UInt8
  | [] => (0, [])
  | byte :: rest =>
    if byte < 0xC0 then (byte.toUInt32, rest)
    else
      let (code, after) := utf8Continue (utf8LeadBits byte) rest
      (if code < 0x80 || code &&& 0xFFFFF800 == 0xD800 || code &&& 0xFFFFFFFE == 0xFFFE then 0xFFFD else code, after)

/-- The bytes after the next character of a C string ({lit}`SQLITE_SKIP_UTF8`): one byte, and
the continuation bytes after a lead byte of {lit}`0xC0` or more. -/
def utf8Skip : List UInt8 → List UInt8
  | [] => []
  | byte :: rest => if byte < 0xC0 then rest else rest.dropWhile (· &&& 0xC0 == 0x80)

/-- The UTF-8 bytes of a code point below {lit}`0x200000`, in one to four bytes, as SQLite's
{lit}`char` and {lit}`sqlite3AppendOneUtf8Character` write them. -/
def utf8Bytes (code : UInt32) : List UInt8 :=
  let byte := fun (base : UInt32) (shift : UInt32) (mask : UInt32) => (base + ((code >>> shift) &&& mask)).toUInt8
  if code < 0x80 then [code.toUInt8]
  else if code < 0x800 then [byte 0xC0 6 0x1F, byte 0x80 0 0x3F]
  else if code < 0x10000 then [byte 0xE0 12 0x0F, byte 0x80 6 0x3F, byte 0x80 0 0x3F]
  else [byte 0xF0 18 0x07, byte 0x80 12 0x3F, byte 0x80 6 0x3F, byte 0x80 0 0x3F]

end Belay.Sqlite.Model.Resolved
