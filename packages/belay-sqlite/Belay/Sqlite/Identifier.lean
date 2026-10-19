import Belay.Sqlite.ByteText

set_option doc.verso true

/-! Names of tables, columns, indexes and sources as bytes (ADR 0013, step 8). SQLite
keeps a name as the bytes that the SQL text wrote, after it removes the quotes, and
compares names with ASCII case folding ({lit}`sqlite3StrICmp`). The kernel reduces a
byte list quickly, where it inspects a {lean}`String` character by character. -/

namespace Belay.Sqlite

/-- The bytes of a table, column, index or source name, without its quotes. For example
{lit}`name! "t"` names the table {lit}`t`. The one field keeps names apart from other
byte lists: the JSON form of a name is a string and its source form is a
{lit}`name!` literal. -/
structure Identifier where
  /-- The bytes of the name as written. -/
  bytes : List UInt8
  deriving DecidableEq, Hashable, Inhabited

/-- A fixed name, written {lit}`name! "t"` for {lit}`Identifier.mk [116]`. The kernel sees
the byte list of {lit}`bytes!`. -/
macro "name! " text:str : term => `(Identifier.mk (bytes! $text))

/-- A name from its bytes. -/
def Identifier.ofBytes (bytes : List UInt8) : Identifier := ⟨bytes⟩

/-- A name from its UTF-8 text, for programs that read names as text, such as the JSON
codec. Lean source writes a fixed name as {lit}`name! "t"`, which the kernel needs not
decode. -/
def Identifier.ofString (text : String) : Identifier := ⟨text.toUTF8.toList⟩

/-- The name with ASCII capitals folded to lowercase ({name}`lowerAscii`); every other
byte stays. Two names are the same name for SQLite when their folds are equal. For
example the folds of {lit}`Ab_É` and {lit}`aB_É` are equal, and the fold of {lit}`É`
is not that of {lit}`é`. -/
def Identifier.folded (name : Identifier) : List UInt8 := name.bytes.map lowerAscii

/-- Whether two names are the same name for SQLite: equal after
{name}`Identifier.folded`. -/
def Identifier.sameName (left right : Identifier) : Bool := left.folded == right.folded

/-- Every name is the same name as itself. -/
@[simp] theorem Identifier.sameName_self (name : Identifier) : name.sameName name = true := by
  simp [Identifier.sameName]

/-- Whether the name is a keyword without ASCII case ({name}`equalsKeyword`); the keyword
is given in lowercase. -/
def Identifier.isKeyword (name : Identifier) (keyword : List UInt8) : Bool :=
  equalsKeyword name.bytes keyword

/-- Whether a byte continues a UTF-8 sequence: {lit}`10xxxxxx`. -/
def isContinuationByte (byte : UInt8) : Bool := byte &&& 0xc0 == 0x80

/-- The characters of UTF-8 bytes. A sequence of two, three or four bytes with the right
continuation bytes gives its character; any other byte gives the character with the
byte's value as its code point. The recursion is structural on the list, so the kernel
reduces it as fast as the bytes. -/
def decodeUtf8 : List UInt8 → List Char
  | [] => []
  | first :: rest =>
    let bits := fun (byte : UInt8) (mask : UInt8) => (byte &&& mask).toNat
    match rest with
    | second :: third :: fourth :: after =>
      if first &&& 0xf8 == 0xf0 && isContinuationByte second && isContinuationByte third
          && isContinuationByte fourth then
        Char.ofNat (bits first 0x07 * 0x40000 + bits second 0x3f * 0x1000 + bits third 0x3f * 0x40
          + bits fourth 0x3f) :: decodeUtf8 after
      else if first &&& 0xf0 == 0xe0 && isContinuationByte second && isContinuationByte third then
        Char.ofNat (bits first 0x0f * 0x1000 + bits second 0x3f * 0x40 + bits third 0x3f)
          :: decodeUtf8 (fourth :: after)
      else if first &&& 0xe0 == 0xc0 && isContinuationByte second then
        Char.ofNat (bits first 0x1f * 0x40 + bits second 0x3f) :: decodeUtf8 (third :: fourth :: after)
      else Char.ofNat first.toNat :: decodeUtf8 (second :: third :: fourth :: after)
    | [second, third] =>
      if first &&& 0xf0 == 0xe0 && isContinuationByte second && isContinuationByte third then
        [Char.ofNat (bits first 0x0f * 0x1000 + bits second 0x3f * 0x40 + bits third 0x3f)]
      else if first &&& 0xe0 == 0xc0 && isContinuationByte second then
        Char.ofNat (bits first 0x1f * 0x40 + bits second 0x3f) :: decodeUtf8 [third]
      else Char.ofNat first.toNat :: decodeUtf8 [second, third]
    | [second] =>
      if first &&& 0xe0 == 0xc0 && isContinuationByte second then
        [Char.ofNat (bits first 0x1f * 0x40 + bits second 0x3f)]
      else Char.ofNat first.toNat :: decodeUtf8 [second]
    | [] => [Char.ofNat first.toNat]

/-- The text of a name, for messages, output column names and the JSON form: the bytes
decoded as UTF-8 ({name}`decodeUtf8`). A name that the parser wrote is always valid
UTF-8; other bytes give one character for each byte. -/
def Identifier.text (name : Identifier) : String := String.ofList (decodeUtf8 name.bytes)

instance : ToString Identifier := ⟨Identifier.text⟩

/-- A name as Lean source: {lit}`name! "t"` for a name whose bytes are valid UTF-8, else
{lit}`Identifier.mk` of the byte list. The generated input modules print names in this
form. -/
instance : Repr Identifier where
  reprPrec name precedence :=
    match String.fromUTF8? (ByteArray.mk name.bytes.toArray) with
    | some text => Repr.addAppParen ("name! " ++ text.quote) precedence
    | none => Repr.addAppParen ("Identifier.mk " ++ repr name.bytes) precedence

end Belay.Sqlite
