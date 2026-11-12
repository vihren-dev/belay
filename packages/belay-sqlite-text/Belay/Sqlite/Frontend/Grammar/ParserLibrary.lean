set_option doc.verso true

/-! The C API of the SQLite parser library ({lit}`parser/library.h`), called in the Lean process.
The functions are native code: a file that calls them while it elaborates needs the precompiled
modules of this package, which Lake loads for {lit}`lake build`, {lit}`lake lean` and the editor's
server. Each call gives the library's JSON document as text; {lit}`ParseTree.lean` reads it. -/

namespace Belay.Sqlite.ParserLibrary

/-- The library's metadata document: its API version, the SQLite releases, and the dialects
with the grammar identity of each. It fails only when the library cannot allocate the
document. -/
@[extern "belay_parser_metadata"]
opaque metadata : IO String

/-- The parse document of SQL text, as its bytes, with the grammar whose identity is
{lit}`grammar`: the syntax tree, or the offset where SQLite's grammar rejects the text (offset 0
for bytes that are not UTF-8) or where the parser's size limits stop it. It fails when the library
has no grammar of that identity. -/
@[extern "belay_parser_parse"]
opaque parse (grammar : @& String) (sql : @& ByteArray) : IO String

end Belay.Sqlite.ParserLibrary
