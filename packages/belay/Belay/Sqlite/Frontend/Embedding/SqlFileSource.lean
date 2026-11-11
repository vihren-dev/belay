import Lean.Compiler.ModPkgExt
import Lean.Elab.Term

set_option doc.verso true

namespace Belay.Sqlite
open Lean System

/-- SQL read from the package that owns a Lean source file. Keep the relative path and
package identity in compiled records; the root is only for current file access and must
never be serialized, because it is specific to this machine and checkout. -/
structure SqlFileSource where
  /-- The compiler's package identity, including its native symbol disambiguation. -/
  package : PkgId
  /-- The directory the file was read from: the discovered package directory, or the
  explicit root of {lit}`readSqlFileSourceAtRoot`. -/
  root : FilePath
  /-- The SQL path relative to that package directory. -/
  path : FilePath
  /-- The unchanged file text, including comments and original line endings. -/
  text : String

/-- Decode the package directories recorded by pinned Lake's manifest. Dependency names
may be aliases, so their explicit directories establish the source association. The root
entry has no directory field and is selected by its compiler package identity. -/
private def manifestPackageRoots (directory : FilePath) (package : PkgId)
    (manifest : Json) : Except String (Array FilePath) := do
  let mut roots := #[]
  if (← manifest.getObjValAs? String "name") == package then
    roots := roots.push directory
  for entry in ← manifest.getObjValAs? (Array Json) "packages" do
    let root ← (do
      match ← entry.getObjValAs? String "type" with
      | "path" => return directory / (← entry.getObjValAs? String "dir")
      | "git" =>
        let packages ← manifest.getObjValAs? String "packagesDir"
        let name ← entry.getObjValAs? String "name"
        let root := directory / packages / name
        return match entry.getObjValAs? String "subDir" with
          | .ok subDir => root / subDir
          | .error _ => root
      | kind => throw s!"unsupported package source {kind}" : Except String FilePath)
    roots := roots.push root
  return roots

/-- Add each ancestor once. Source and workspace search paths can share many ancestors. -/
private def addAncestors (directories : Array FilePath) (start : FilePath) : Array FilePath := Id.run do
  let mut result := directories
  let mut directory := some start
  while let some current := directory do
    if !result.contains current then result := result.push current
    directory := current.parent
  return result

/-- A manifest candidate owns this source only when the source is below its real directory. -/
private def containsSource (root source : FilePath) : Bool :=
  root.components.isPrefixOf source.components

/-- Find the package of a Lean source from existing Lake manifests and the compiler's
package identity. Search the source, workspace and source-search-path ancestors; resolve
manifest dependency paths relative to their workspace. A nested unrelated lakefile cannot
change the root. Missing or ambiguous metadata gives an error instead of guessing a root. -/
def sqlPackageRoot (leanFile : FilePath) (package : PkgId) : IO FilePath := do
  let source ← IO.FS.realPath leanFile
  let mut directories := addAncestors #[] (source.parent.getD source)
  directories := addAncestors directories (← IO.currentDir)
  for path in SearchPath.parse ((← IO.getEnv "LEAN_SRC_PATH").getD "") do
    if ← path.pathExists then
      directories := addAncestors directories (← IO.FS.realPath path)
  let mut roots : Array FilePath := #[]
  for directory in directories do
    let path := directory / "lake-manifest.json"
    if !(← path.pathExists) then continue
    let text ← IO.FS.readFile path
    let candidates ← match Json.parse text >>= manifestPackageRoots directory package with
      | .ok candidates => pure candidates
      | .error error => throw <| IO.userError s!"cannot read package metadata {path}: {error}; run lake update"
    for candidate in candidates do
      if !(← candidate.pathExists) then continue
      let root ← IO.FS.realPath candidate
      if containsSource root source && !roots.contains root then roots := roots.push root
  match roots.toList with
  | [root] => return root
  | [] => throw <| IO.userError s!"cannot find the package {package} of {leanFile}; compile with lake build and keep its package manifest available, or set belay.sql.packageRoot to the package directory relative to the Lean file's directory"
  | _ => throw <| IO.userError s!"ambiguous package roots for {leanFile}: {roots}; set belay.sql.packageRoot to the intended directory, written relative to the Lean file's directory"

/-- Read a package-relative SQL file below an explicit package root. This is the primitive
beneath automatic discovery and the {lit}`belay.sql.packageRoot` option. The root controls
current file access only: the compiled identity is the supplied package and the relative
path. Absolute paths and paths that leave the root are errors, so that an identity cannot
name a machine-specific location. The SQL text is unchanged. -/
def readSqlFileSourceAtRoot (root : FilePath) (package : PkgId) (path : FilePath) : IO SqlFileSource := do
  if path.isAbsolute then
    throw <| IO.userError s!"SQL path {path} is absolute; use a path relative to the package"
  let relative := path.normalize
  if relative.components.contains ".." then
    throw <| IO.userError s!"SQL path {path} leaves the package; use a path below the package root"
  unless ← root.isDir do
    throw <| IO.userError s!"the SQL package root {root} is not a directory; correct the root, or set belay.sql.packageRoot to the package directory relative to the Lean file's directory"
  let root ← IO.FS.realPath root
  let text ← try IO.FS.readFile (root / relative)
    catch error => throw <| IO.userError s!"cannot read SQL file {path} in package {root}: {error}; check that the path is relative to the package root and that the file exists and is readable"
  return { package, root, path := relative, text }

/-- Read a package-relative SQL file for the supplied Lean source and compiler package, using
the root that {name}`sqlPackageRoot` discovers. Use the caller's package identity, not the
Belay dependency's identity. -/
def readSqlFileSource (leanFile : FilePath) (package : PkgId) (path : FilePath) : IO SqlFileSource := do
  readSqlFileSourceAtRoot (← sqlPackageRoot leanFile package) package path

end Belay.Sqlite
