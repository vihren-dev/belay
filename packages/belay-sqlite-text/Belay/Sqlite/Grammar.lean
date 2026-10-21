import Lean.Data.Json

set_option doc.verso true

/-! The choice of the parser library's grammar for a SQLite release and build, as the Python
binding chooses it ({lit}`belay/sqlite/dialects.py`) for a profile without compile options: the
dialect of the release with no grammar options. The choice never falls back to another
dialect. -/

namespace Belay.Sqlite

open Lean (Json)

/-- A SQLite release and the source id of its build, as {lit}`sqlite_version()` and
{lit}`sqlite_source_id()` report them. -/
structure Release where
  /-- The release, for example {lit}`3.51.0`. -/
  version : String
  /-- The build of the release. -/
  sourceId : String
  deriving Repr, BEq

/-- SQLite 3.51.0 in the build that the model describes, the default release of the verifier. -/
def Release.default : Release :=
  { version := "3.51.0", sourceId := "2025-11-04 19:38:17 fb2c931ae597f8d00a37574ff67aeed3eced4e5547f9120744ae4bfa8e74527b" }

/-- What a user can do when the parser library has no grammar for a release. -/
def grammarAdvice : String :=
  "; select SQLite 3.51.0 or 3.46.0, or rebuild the parser library with a dialect of this release"

/-- The grammar identity of the release's dialect without grammar options, from the library's
metadata document; an error names the release and what the library has. -/
def findGrammar (metadata : Json) (release : Release) : Except String String := do
  let releases ← (← metadata.getObjVal? "releases").getArr?
  let dialects ← (← metadata.getObjVal? "dialects").getArr?
  let some entry := releases.find? (fun entry => (entry.getObjValAs? String "version").toOption == some release.version)
    | throw s!"the parser library has no SQLite {release.version}"
  unless (← entry.getObjValAs? String "sourceId") == release.sourceId do
    throw s!"SQLite {release.version} with source id {release.sourceId} is another build than the parser's"
  let matching := dialects.filter fun dialect =>
    (dialect.getObjValAs? String "version").toOption == some release.version &&
      (dialect.getObjValAs? (Array Json) "grammarOptions").toOption.map (·.isEmpty) == some true
  let some dialect := matching[0]? | throw s!"the parser library has no dialect of SQLite {release.version} without grammar options"
  dialect.getObjValAs? String "grammar"

/-- The grammar identity of the release's dialect ({name}`findGrammar`); an error also says what
the user can do. -/
def selectGrammar (metadata : Json) (release : Release) : Except String String :=
  (findGrammar metadata release).mapError (· ++ grammarAdvice)

end Belay.Sqlite
