import Belay

/-! A fixture of `tests/surface_parser_test.py`: `Belay.Sqlite.selectGrammar` over a small
metadata document. It finds the dialect of a release without grammar options, and its errors
for another release or another build end with what the user can do. -/

open Belay.Sqlite Lean

/-- A metadata document with one release, 3.51.0, and its two dialects. -/
def metadata : Json := Json.mkObj [
  ("releases", Json.arr #[Json.mkObj [("version", "3.51.0"), ("sourceId", "build")]]),
  ("dialects", Json.arr #[
    Json.mkObj [("version", "3.51.0"), ("grammarOptions", Json.arr #["SQLITE_OMIT_TRIGGER"]), ("grammar", "b")],
    Json.mkObj [("version", "3.51.0"), ("grammarOptions", Json.arr #[]), ("grammar", "a")]])]

#guard (selectGrammar metadata { version := "3.51.0", sourceId := "build" }).toOption == some "a"
#guard match selectGrammar metadata { version := "3.46.0", sourceId := "build" } with
  | .error message => message.endsWith grammarAdvice | .ok _ => false
#guard match selectGrammar metadata { version := "3.51.0", sourceId := "other" } with
  | .error message => message.endsWith grammarAdvice | .ok _ => false
