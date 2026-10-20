import Belay.Sqlite.Identifier

set_option doc.verso true

/-! Checked examples of names as bytes: SQLite's ASCII-only case folding, the text of a
name for messages, and the source form of the generated input modules. -/

namespace Belay.Sqlite.IdentifierExamples

open Belay.Sqlite

-- ASCII capitals fold; other bytes, also those of non-ASCII letters, stay.
#guard (name! "ÄInvoices").folded == bytes! "Äinvoices"
#guard (name! "Ab_É").sameName (name! "aB_É") && !(name! "É").sameName (name! "é")
#guard (name! "ROWID").isKeyword (bytes! "rowid")
-- The text of a name is its UTF-8 text; bytes that are not UTF-8 give one character each.
#guard (name! "Ünit \"q\"").text == "Ünit \"q\""
#guard (Identifier.ofBytes [0x61, 0xff]).text == String.ofList ['a', Char.ofNat 0xff]
#guard Identifier.ofString "Ünit" == name! "Ünit"
-- The source form is the literal, or the byte list when the bytes are not UTF-8.
#guard reprStr (name! "a\"b") == "name! \"a\\\"b\""
#guard reprStr (Identifier.ofBytes [0xff]) == "Identifier.mk [255]"

end Belay.Sqlite.IdentifierExamples
