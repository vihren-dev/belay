import Belay.Sqlite.Grammar
import Belay.Sqlite.ParseTree
import Belay.Sqlite.ParserLibrary

set_option doc.verso true

/-! SQL text parsed in the Lean process with the parser library's grammar of a release. -/

namespace Belay.Sqlite

open Lean (Json)

/-- The library's metadata document, read once for the process. -/
initialize parserMetadata : IO.Ref (Option Json) ← IO.mkRef none

/-- The metadata of the loaded library, read on the first call. -/
def loadedMetadata : IO Json := do
  if let some metadata ← parserMetadata.get then return metadata
  match Json.parse (← ParserLibrary.metadata) with
  | .ok metadata => parserMetadata.set (some metadata); return metadata
  | .error message => throw <| IO.userError s!"the parser library's metadata is not JSON: {message}"

/-- Parse SQL text, as its UTF-8 bytes, with the grammar of the release: the tree, or where
SQLite's grammar rejects the text. It fails when the library has no grammar for the release or
gives a document that is not a parse document. For example,
{lit}`parseSql Release.default "SELECT 1;".toUTF8` gives a tree. -/
def parseSql (release : Release) (sql : ByteArray) : IO ParseResult := do
  let grammar ← IO.ofExcept ((selectGrammar (← loadedMetadata) release).mapError IO.userError)
  match decodeParse grammar sql.size (← ParserLibrary.parse grammar sql) with
  | .ok result => return result
  | .error message => throw <| IO.userError s!"the parser library's parse document is not usable: {message}"

end Belay.Sqlite
