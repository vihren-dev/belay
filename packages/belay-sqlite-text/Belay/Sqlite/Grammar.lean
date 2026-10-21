import Lean.Data.Json

set_option doc.verso true

/-! The choice of the parser library's grammar for a SQLite release, its build and its compile
options. A dialect is a release with the grammar options in effect; the library's metadata lists
each built dialect with its grammar identity. The choice never falls back to another dialect: a
release without a built dialect has no grammar. -/

namespace Belay.Sqlite

open Lean (Json)

/-- A SQLite release, the source id of its build and its compile options, as
{lit}`sqlite_version()`, {lit}`sqlite_source_id()` and {lit}`PRAGMA compile_options` report
them. -/
structure Release where
  /-- The release, for example {lit}`3.51.0`. -/
  version : String
  /-- The build of the release. -/
  sourceId : String
  /-- The compile options, for example {lit}`THREADSAFE=1`; use {lit}`[]` for a default build. -/
  compileOptions : List String := []
  deriving Repr, BEq

/-- SQLite 3.51.0 in the build that the model describes, the default release of the verifier. -/
def Release.default : Release :=
  { version := "3.51.0", sourceId := "2025-11-04 19:38:17 fb2c931ae597f8d00a37574ff67aeed3eced4e5547f9120744ae4bfa8e74527b" }

/-- What a user can do when the parser library has no grammar for a release. -/
def grammarAdvice : String :=
  "; select SQLite 3.51.0 or 3.46.0, or rebuild the parser library with a dialect of this release"

/-- The grammar options among the compile options, as sorted macro names without repeats.
{lit}`PRAGMA compile_options` reports {lit}`SQLITE_OMIT_TRIGGER` as {lit}`OMIT_TRIGGER`, and a
value after {lit}`=`; the grammar's conditionals test only whether a macro is defined, so the
choice compares names without values. For example, the compile options
{lit}`["THREADSAFE=1", "OMIT_TRIGGER"]` with the grammar options {lit}`["SQLITE_OMIT_TRIGGER"]`
give {lit}`["SQLITE_OMIT_TRIGGER"]`. -/
def optionsInEffect (compileOptions grammarOptions : List String) : List String :=
  let names := compileOptions.map fun option => "SQLITE_" ++ (option.splitOn "=").headD ""
  ((grammarOptions.filter names.contains).eraseDups.toArray.qsort (· < ·)).toList

/-- The grammar identity of the release's dialect with the grammar options in effect, from the
library's metadata document; an error names the release and what the library has. -/
def findGrammar (metadata : Json) (release : Release) : Except String String := do
  let releases ← (← metadata.getObjVal? "releases").getArr?
  let dialects ← (← metadata.getObjVal? "dialects").getArr?
  let some entry := releases.find? (fun entry => (entry.getObjValAs? String "version").toOption == some release.version)
    | throw s!"the parser library has no SQLite {release.version}"
  unless (← entry.getObjValAs? String "sourceId") == release.sourceId do
    throw s!"SQLite {release.version} with source id {release.sourceId} is another build than the parser's"
  let options := optionsInEffect release.compileOptions (← entry.getObjValAs? (List String) "grammarOptions")
  let matching := dialects.filter fun dialect =>
    (dialect.getObjValAs? String "version").toOption == some release.version &&
      (dialect.getObjValAs? (Array String) "grammarOptions").toOption.map (fun names => (names.qsort (· < ·)).toList)
        == some options
  let some dialect := matching[0]?
    | throw s!"the parser library has no dialect of SQLite {release.version} with the grammar options {options}"
  dialect.getObjValAs? String "grammar"

/-- The grammar identity of the release's dialect ({name}`findGrammar`); an error also says what
the user can do. -/
def selectGrammar (metadata : Json) (release : Release) : Except String String :=
  (findGrammar metadata release).mapError (· ++ grammarAdvice)

end Belay.Sqlite
