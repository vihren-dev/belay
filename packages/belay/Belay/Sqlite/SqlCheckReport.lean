import Belay.Sqlite.SqlSourceRecord

set_option doc.verso true

/-! The result of checking the compiled SQL-file records of a library against the files on disk
(ADR 0017, S7). This module is the pure part of the checker: it decides if a source is fresh
and writes the report. It does not read files and does not import Lake, so tests can use it
without a Lake workspace. -/

namespace Belay.Sqlite

open Lean System

/-- What the current file says about a recorded source. -/
inductive SourceState where
  /-- The file has the recorded hash. -/
  | fresh
  /-- The file exists with another hash, so the library was built from other text. -/
  | changed
  /-- The file does not exist in its package. -/
  | missing
  deriving BEq, Repr

/-- Compare the recorded hash with the current hash of the file; {lean}`none` is a missing file. -/
def sourceState (recorded : UInt64) (current : Option UInt64) : SourceState :=
  match current with
  | none => .missing
  | some hash => if hash == recorded then .fresh else .changed

/-- One distinct source of a library, with the declarations that were built from it. -/
structure CheckedSource where
  /-- The package that owns the file. -/
  package : String
  /-- The path relative to that package. -/
  path : String
  /-- The result of the comparison. -/
  state : SourceState
  /-- The declarations that used this source, in record order. -/
  declarations : Array Name

/-- A record with the file it names, found in the current workspace. The checker resolves the
file; this module only groups the results. -/
structure ResolvedUse where
  /-- The record. -/
  use : SqlSourceUse
  /-- The file, with its directory resolved, so two ways to name one file give one value. -/
  file : FilePath
  /-- The path to show: relative to the owning package when the file is inside it. -/
  shown : String

/-- The distinct sources of the records: one for each file and text hash, however many declarations
or modules read it. A source keeps the declarations of all its records. -/
def groupSources (resolved : Array (ResolvedUse × Option UInt64)) : Array CheckedSource := Id.run do
  let mut groups : Array (FilePath × UInt64 × CheckedSource) := #[]
  for (item, current) in resolved do
    let declarations := item.use.declaration.toArray
    match groups.findIdx? fun (file, hash, _) => file == item.file && hash == item.use.hash with
    | some index =>
      groups := groups.modify index fun (file, hash, source) =>
        (file, hash, { source with declarations := source.declarations ++ declarations })
    | none =>
      let state := sourceState item.use.hash current
      let source : CheckedSource := { package := item.use.package, path := item.shown, state, declarations }
      groups := groups.push (item.file, item.use.hash, source)
  return groups.map (·.2.2)

/-- The check of one library: how many compiled modules were inspected, and its distinct sources. -/
structure LibraryCheck where
  /-- The library name, as {lit}`lake build` takes it. -/
  library : String
  /-- The number of compiled modules of the library that were read. -/
  modules : Nat
  /-- The distinct sources that these modules and their imports recorded. -/
  sources : Array CheckedSource

/-- The sources of the library that are not fresh. -/
def LibraryCheck.stale (check : LibraryCheck) : Array CheckedSource :=
  check.sources.filter (·.state != .fresh)

/-- The text of the check of one library: the totals, then each stale source with the command that
rebuilds the library. A library with no SQL sources reports zero. -/
def LibraryCheck.render (check : LibraryCheck) : String :=
  let stale := check.stale
  let header := s!"library {check.library}: {check.modules} modules, {check.sources.size} SQL sources, {stale.size} stale"
  let lines := stale.toList.map fun source =>
    let what := if source.state == .missing then "is missing" else "changed since the library was built"
    let users := ", ".intercalate (source.declarations.toList.map toString)
    let used := if users.isEmpty then "" else s!" (used by {users})"
    s!"  {source.package}: {source.path} {what}{used}; rebuild with: lake build {check.library}"
  let note := if stale.isEmpty then [] else
    [s!"  lake build rebuilds {check.library} after an SQL edit only if its lakefile lists the SQL files as needs of the library (input_dir); otherwise change a Lean file of the library, or run lake clean first"]
  "\n".intercalate (header :: lines ++ note)

/-- The exit code of a run: 0 when every inspected source is fresh, 1 when a source is stale, and 2
when a library could not be inspected, which is not evidence of zero sources. -/
def exitCodeOf (checks : Array LibraryCheck) (problems : Array String) : UInt32 :=
  if !problems.isEmpty then 2
  else if checks.any (!·.stale.isEmpty) then 1
  else 0

end Belay.Sqlite
