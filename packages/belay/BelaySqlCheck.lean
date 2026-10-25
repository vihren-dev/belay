import Lake
import Lake.Load
import Belay.Sqlite.SqlCheckReport

set_option doc.verso true

/-! {lit}`lake exe belay-sql-check [--library NAME]` (ADR 0017, S7): compare the SQL files that the
compiled libraries of the current package read with the files on disk. The tool only inspects the
existing build. It never builds a library, and it never writes a manifest, so a stale library is
reported before any rebuild. It is the only module of the surface that imports Lake. -/

open Lean Lake System Belay.Sqlite

/-- The records of one module's entry array, as the elaborator stored them. -/
private unsafe def decodeUsesUnsafe (entries : Array EnvExtensionEntry) : Array SqlSourceUse :=
  unsafeCast entries

/-- Read the stored records. Only the extension of {lit}`SqlSourceRecord` stores values of this type. -/
@[implemented_by decodeUsesUnsafe]
private opaque decodeUses (entries : Array EnvExtensionEntry) : Array SqlSourceUse

/-- The records that a compiled module stored itself. -/
private def storedUses (data : ModuleData) : Array SqlSourceUse :=
  match data.entries.find? (·.1 == sqlSourceUseExtension.name) with
  | some (_, entries) => decodeUses entries
  | none => #[]

/-- Modules of the toolchain, which never record SQL files and are large to read. -/
private def inToolchain (module : Name) : Bool :=
  [`Init, `Std, `Lean, `Lake].contains module.getRoot

/-- What the walk over a library's compiled modules found. -/
private structure Walk where
  /-- The names of the modules read so far. -/
  seen : NameSet := {}
  /-- Every record of those modules, in read order. -/
  uses : Array SqlSourceUse := #[]
  /-- Compiled modules that could not be read. -/
  problems : Array String := #[]

/-- Read one compiled module and everything it imports. A module that cannot be found or read is a
problem, because the library then has no evidence about its sources. -/
private partial def walkModule (workspace : Workspace) (module : Name) (walk : Walk) : IO Walk := do
  if walk.seen.contains module || inToolchain module then return walk
  let walk := { walk with seen := walk.seen.insert module }
  try
    -- Lean's search path takes the first folder that has the module's root name, but the
    -- model, text and surface packages share the root Belay, so the workspace decides.
    let file ← match workspace.findModule? module with
      | some found => pure found.oleanFile
      | none => findOLean module
    unless ← file.pathExists do
      return { walk with problems := walk.problems.push s!"module {module} has no compiled file {file}" }
    let (data, _) ← readModuleData file
    let mut walk := { walk with uses := walk.uses ++ storedUses data }
    for import_ in data.imports do
      walk ← walkModule workspace import_.module walk
    return walk
  catch error =>
    return { walk with problems := walk.problems.push s!"cannot read the compiled module {module}: {error}" }

/-- The packages of the workspace that have this original name, which is the package identity stored
in the records. -/
private def packagesNamed (workspace : Workspace) (name : String) : Array Package :=
  workspace.packages.filter (·.origName.toString (escape := false) == name)

/-- Compare the records of one distinct source with its file in the owning package. -/
private def checkSource (workspace : Workspace) (uses : Array SqlSourceUse) (use : SqlSourceUse) :
    IO (Except String CheckedSource) := do
  let declarations := uses.filterMap fun other => if other.sameSource use then other.declaration else none
  match packagesNamed workspace use.package with
  | #[package] =>
    let file := package.dir / use.path
    let current ← if ← file.pathExists then some <$> sqlTextHash <$> IO.FS.readFile file else pure none
    return .ok { package := use.package, path := use.path, state := sourceState use.hash current, declarations }
  | #[] => return .error s!"a record names package {use.package}, which is not in this workspace"
  | _ => return .error s!"a record names package {use.package}, which several packages of this workspace have"

/-- Check one library: read its compiled modules, then compare each distinct source with its file. -/
private def checkLibrary (workspace : Workspace) (library : LeanLib) : IO (LibraryCheck × Array String) := do
  let modules ← library.getModuleArray
  let mut walk : Walk := {}
  for module in modules do
    walk ← walkModule workspace module.name walk
  let mut sources := #[]
  let mut problems := walk.problems
  let mut distinct : Array SqlSourceUse := #[]
  for use in walk.uses do
    unless distinct.any use.sameSource do distinct := distinct.push use
  for use in distinct do
    match ← checkSource workspace walk.uses use with
    | .ok source => sources := sources.push source
    | .error problem => problems := problems.push problem
  return ({ library := library.name.toString (escape := false), modules := modules.size, sources }, problems)

/-- The Lake environment of the running toolchain. -/
private def lakeEnvironment : IO Lake.Env := do
  let (elan?, lean?, lake?) ← findInstall?
  let some lean := lean? | throw <| IO.userError "cannot find the Lean installation"
  let some lake := lake? | throw <| IO.userError "cannot find the Lake installation"
  (Env.compute lake lean elan?).toIO fun message => IO.userError message

/-- Load the workspace of the current directory from its manifest. A missing manifest is an error,
because loading would then write one. -/
private def loadCurrentWorkspace : IO Workspace := do
  let directory ← IO.FS.realPath (← IO.currentDir)
  unless ← (directory / "lake-manifest.json").pathExists do
    throw <| IO.userError s!"{directory} has no lake-manifest.json; build the package once with lake build"
  let config : LoadConfig := { lakeEnv := ← lakeEnvironment, wsDir := directory }
  let log (entry : LogEntry) : BaseIO Unit := (IO.eprintln entry.toString).catchExceptions fun _ => pure ()
  match ← (loadWorkspace config).run?' log with
  | some workspace => return workspace
  | none => throw <| IO.userError "cannot load the Lake workspace"

/-- The libraries to check: the one named, or every library of the root package. -/
private def selectLibraries (workspace : Workspace) (name? : Option String) : Except String (Array LeanLib) :=
  let libraries := workspace.root.leanLibs
  match name? with
  | none => .ok libraries
  | some name =>
    match libraries.filter (·.name.toString (escape := false) == name) with
    | #[] => .error s!"the package has no library {name}; its libraries are {", ".intercalate (libraries.toList.map (·.name.toString (escape := false)))}"
    | selected => .ok selected

/-- Run the check and print its report. -/
private def run (name? : Option String) : IO UInt32 := do
  let workspace ← loadCurrentWorkspace
  Lean.searchPathRef.set workspace.augmentedLeanPath
  let libraries ← IO.ofExcept (selectLibraries workspace name?)
  let mut checks := #[]
  let mut problems := #[]
  for library in libraries do
    let (check, found) ← checkLibrary workspace library
    checks := checks.push check
    problems := problems ++ found
    IO.println check.render
  for problem in problems do IO.eprintln s!"error: {problem}"
  return exitCodeOf checks problems

/-- The entry point; see the module documentation. -/
def main (arguments : List String) : IO UInt32 := do
  let name? ← match arguments with
    | [] => pure none
    | ["--library", name] => pure (some name)
    | _ => throw <| IO.userError "usage: lake exe belay-sql-check [--library NAME]"
  try run name?
  catch error =>
    IO.eprintln s!"error: {error}"
    return 2
