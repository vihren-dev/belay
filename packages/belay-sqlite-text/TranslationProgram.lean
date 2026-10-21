import Belay.Sqlite.Parse
import Belay.Sqlite.TranslationRequest

/-! The translation program of the conformance harness: it reads one request on each line of
standard input and writes one answer line for each ({lit}`Belay/Sqlite/TranslationRequest.lean`
describes both). One process translates a whole batch, so the shared libraries load and the
model's modules initialize once. -/

open Belay.Sqlite Belay.Sqlite.TranslationRequest Lean

/-- The answer to one request line: the grammar of the request's profile parses the text, and the
translation maps the parse. -/
def answerLine (metadata : Json) (line : String) : IO Json := do
  match decodeRequest line with
  | .error message => return errorAnswer s!"the request is not usable: {message}"
  | .ok request =>
    match selectGrammar metadata request.release with
    | .error message => return noParserAnswer message
    | .ok grammar =>
      match decodeParse grammar request.sql.size (← ParserLibrary.parse grammar request.sql) with
      | .ok result => return answer request result
      | .error message => return errorAnswer s!"the parser library's parse document is not usable: {message}"

/-- Answer each line until the end of standard input, and write each answer at once, so that the
harness can read it before it sends the next request. A failure of one request does not stop the
batch. -/
def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let metadata ← loadedMetadata
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result ← try answerLine metadata line catch error => pure (errorAnswer error.toString)
    output.putStrLn result.compress
    output.flush
  return 0
