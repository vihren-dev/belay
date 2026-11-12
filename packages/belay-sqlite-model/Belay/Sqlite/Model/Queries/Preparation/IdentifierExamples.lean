import Belay.Sqlite.Model.Shared.Values.Identifier

set_option doc.verso true

namespace Belay.Sqlite.Model.IdentifierExamples

open Belay.Sqlite.Model

#guard (name! "ROWID").isKeyword (bytes! "rowid")
-- The text of a name is its UTF-8 text; bytes that are not UTF-8 give one character each.
#guard (name! "Ünit \"q\"").text == "Ünit \"q\""
#guard (Identifier.ofBytes [0x61, 0xff]).text == String.ofList ['a', Char.ofNat 0xff]
#guard Identifier.ofString "Ünit" == name! "Ünit"
-- The source form is the literal, or the byte list when the bytes are not UTF-8.
#guard reprStr (name! "a\"b") == "name! \"a\\\"b\""
#guard reprStr (Identifier.ofBytes [0xff]) == "Identifier.mk [255]"

end Belay.Sqlite.Model.IdentifierExamples
