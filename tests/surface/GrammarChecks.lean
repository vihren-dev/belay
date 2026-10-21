import Belay

/-! A fixture of `tests/surface_parser_test.py`: `Belay.Sqlite.selectGrammar` of the text package
over a small metadata document, with the cases that `tests/test_dialect_selection.py` checked in
the Python binding. Each release selects its dialect without grammar options; only grammar options
among the compile options select another dialect, and option values change nothing; an unknown
release, another build, or options without a dialect select no grammar, and the error ends with
what the user can do. -/

open Belay.Sqlite Lean

/-- Two releases; 3.51.0 has a dialect without grammar options and one with UPDATE ... LIMIT. -/
def metadata : Json := Json.mkObj [
  ("releases", Json.arr #[
    Json.mkObj [("version", "3.51.0"), ("sourceId", "build"),
      ("grammarOptions", Json.arr #["SQLITE_ENABLE_UPDATE_DELETE_LIMIT", "SQLITE_OMIT_TRIGGER"])],
    Json.mkObj [("version", "3.46.0"), ("sourceId", "old"), ("grammarOptions", Json.arr #[])]]),
  ("dialects", Json.arr #[
    Json.mkObj [("version", "3.51.0"), ("grammarOptions", Json.arr #[]), ("grammar", "a")],
    Json.mkObj [("version", "3.51.0"), ("grammarOptions", Json.arr #["SQLITE_ENABLE_UPDATE_DELETE_LIMIT"]),
      ("grammar", "b")],
    Json.mkObj [("version", "3.46.0"), ("grammarOptions", Json.arr #[]), ("grammar", "c")]])]

/-- Whether the release selects no grammar, with an error that ends with the advice. -/
def refused (release : Release) : Bool :=
  match selectGrammar metadata release with
  | .error message => message.endsWith grammarAdvice
  | .ok _ => false

#guard (selectGrammar metadata { version := "3.51.0", sourceId := "build" }).toOption == some "a"
#guard (selectGrammar metadata { version := "3.46.0", sourceId := "old" }).toOption == some "c"
#guard optionsInEffect ["THREADSAFE=1", "MAX_COLUMN=2000", "ENABLE_UPDATE_DELETE_LIMIT"]
  ["SQLITE_ENABLE_UPDATE_DELETE_LIMIT"] == ["SQLITE_ENABLE_UPDATE_DELETE_LIMIT"]
/-- The build of 3.51.0 in the metadata, with the compile options. -/
def build (compileOptions : List String) : Release :=
  { version := "3.51.0", sourceId := "build", compileOptions }

#guard (selectGrammar metadata (build ["THREADSAFE=1", "MAX_COLUMN=2000"])).toOption == some "a"
#guard (selectGrammar metadata (build ["THREADSAFE=1", "ENABLE_UPDATE_DELETE_LIMIT=1"])).toOption == some "b"
#guard refused { version := "3.45.0", sourceId := "build" }
#guard refused { version := "3.51.0", sourceId := "other" }
#guard refused (build ["OMIT_TRIGGER"])
