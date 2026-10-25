import Lean.EnvExtension

set_option doc.verso true

/-! The compiled record of an SQL file that a Lean module read (ADR 0017, S7). The record keeps
the owning package, the path relative to that package and a hash of the text with line endings
normalized as Lake normalizes text inputs. It keeps no absolute path, so a relocated package
still maps its records to its own files. This module has no dependency on Lake, so the
elaborator and the separate checker read the same type. -/

namespace Belay.Sqlite

open Lean

/-- The root that the {lit}`belay.sql.packageRoot` option chose for a use. The option value is
relative to the directory of the Lean file of the module that set it, so the checker needs both
to find the file again, also after the package moved. -/
structure SqlRootOverride where
  /-- The module whose Lean file the option value is relative to. -/
  module : Name
  /-- The option value, as written. -/
  root : String
  deriving BEq, Repr, Inhabited

/-- One use of an SQL file by a module: the file's identity and content hash when it was read, and
the declaration that used it when there is one. Several uses of one file are several records with
one source. -/
structure SqlSourceUse where
  /-- The Lake package identity that owns the file. -/
  package : String
  /-- The path relative to the package root, as written in the Lean source. -/
  path : String
  /-- The hash of the line-ending-normalized text, see {lit}`sqlTextHash`. -/
  hash : UInt64
  /-- The declaration that was built from the file, when the form is part of one. -/
  declaration : Option Name := none
  /-- The explicit root, when the option chose one. Without it the package directory is the root. -/
  rootOverride : Option SqlRootOverride := none
  deriving BEq, Repr, Inhabited

/-- The hash of an SQL text for freshness: the same line-ending normalization as Lake's
{lit}`text = true` inputs, so an edit that only changes line endings is not an edit. -/
def sqlTextHash (text : String) : UInt64 := hash text.crlfToLf

/-- Whether two records name the same source, so that a source used by several declarations counts
once. -/
def SqlSourceUse.sameSource (left right : SqlSourceUse) : Bool :=
  left.package == right.package && left.path == right.path && left.hash == right.hash &&
    left.rootOverride == right.rootOverride

/-- The records without exact repeats, in first-seen order. -/
def dedupeSqlSourceUses (uses : List SqlSourceUse) : Array SqlSourceUse :=
  uses.foldl (fun seen use => if seen.contains use then seen else seen.push use) #[]

/-- The records of the current module, exported to its compiled file. Elaboration only adds
records and never reads them back, so the extension accepts additions from any branch of an
asynchronous elaboration. -/
initialize sqlSourceUseExtension : SimplePersistentEnvExtension SqlSourceUse Unit ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ _ => ()
    addImportedFn := fun _ => ()
    toArrayFn := dedupeSqlSourceUses
    asyncMode := .sync
  }

/-- Add a record to the module that is being elaborated. -/
def recordSqlSourceUse (env : Environment) (use : SqlSourceUse) : Environment :=
  sqlSourceUseExtension.addEntry env use

/-- The records that each imported module stored, by import order. -/
def importedSqlSourceUses (env : Environment) : Array (Array SqlSourceUse) :=
  (Array.range env.header.moduleNames.size).map (sqlSourceUseExtension.getModuleEntries env ·)

end Belay.Sqlite
