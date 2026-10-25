import Belay.Sqlite.SqlFileSource
import Belay.Sqlite.SqlSourceRecord

set_option doc.verso true

namespace Belay.Sqlite
open Lean System

/-- The {lit}`belay.sql.packageRoot` option. The empty default keeps automatic discovery. A
nonempty value is a path relative to the directory of the Lean source file, for nested Lake
projects whose package ownership discovery cannot decide. It selects where SQL files are read
now. A compiled record keeps the package, the relative path and, for an explicit root, the option
value with its module, never an absolute path. -/
initialize sqlPackageRootOption : Lean.Option String ←
  Lean.Option.register `belay.sql.packageRoot
    { defValue := "", descr := "package directory for sql_file, relative to the Lean file's directory; empty discovers it" }

/-- Resolve the option value against the Lean source's directory, not the compiler's working
directory. Absolute values and values that do not name an existing directory are errors,
because a machine-specific root would not survive relocation. -/
def sqlOverrideRoot (leanFile : FilePath) (override : String) : IO FilePath := do
  let path : FilePath := override
  if path.isAbsolute then
    throw <| IO.userError s!"belay.sql.packageRoot {override} is absolute; use a path relative to the Lean file's directory"
  let source ← IO.FS.realPath leanFile
  let root := (source.parent.getD ".") / path
  unless ← root.isDir do
    throw <| IO.userError s!"belay.sql.packageRoot {override} selects {root}, which is not a directory; set it to an existing directory, written relative to the Lean file's directory"
  return root

/-- The record of a use of a loaded file by the module that is being elaborated: its package, path
and text hash, the explicit root if the option is set, and the declaration that uses it. -/
def currentSqlSourceUse (source : SqlFileSource) (declaration : Option Name) : CoreM SqlSourceUse := do
  let override := sqlPackageRootOption.get (← getOptions)
  let module := (← getEnv).mainModule
  let rootOverride := if override.isEmpty then none else some ⟨module, override⟩
  return { package := source.package, path := source.path.toString, hash := sqlTextHash source.text,
           declaration, rootOverride }

/-- Load a SQL file at a Lean elaboration form. Lake supplies the owning package identity.
Without the option, existing Lake manifests associate the Lean filename with its package
directory; with it, the explicit root is read through {name}`readSqlFileSourceAtRoot`. Errors
point to the form, including a missing package setup when Lean was invoked without Lake's
module setup, because the compiled record needs the package identity in both modes. A
successful load adds a {name}`SqlSourceUse` to the module, with the declaration being elaborated. -/
def loadSqlFileSource (reference : Syntax) (path : FilePath) : Elab.Term.TermElabM SqlFileSource := do
  let some package := (← getEnv).getModulePackage?
    | throwErrorAt reference "SQL files need the owning package's module setup; compile with lake build or open the Lean file in its Lake project"
  let leanFile ← getFileName
  let override := sqlPackageRootOption.get (← getOptions)
  let source ← try
    if override.isEmpty then readSqlFileSource leanFile package path
    else readSqlFileSourceAtRoot (← sqlOverrideRoot leanFile override) package path
  catch error => throwErrorAt reference error.toMessageData
  let use ← currentSqlSourceUse source (← Elab.Term.getDeclName?)
  modifyEnv (recordSqlSourceUse · use)
  return source

end Belay.Sqlite
