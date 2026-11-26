import LeanCodeStore.Commands
import LeanCodeStore.Facts

/-! Facts of one module, read in the environment of that module and its own imports.

The specification of the Lean code store requires this load: one environment for all
selected modules cannot hold two modules that declare the same name. -/

open Lean

namespace LeanCodeStore

/-- The names that the `.ilean` file of a module refers to, as constants of other modules.

The Python side folds these mention targets, so it needs their facts. -/
def ileanTargets (path : System.FilePath) : IO (Array Name) := do
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let references ← IO.ofExcept <| json.getObjVal? "references"
  let .obj entries := references | throw <| IO.userError s!"{path}: field references is not an object; rebuild the module with the pinned Lean toolchain"
  let mut names := #[]
  for (key, _) in entries.toArray do
    let ident ← IO.ofExcept <| Json.parse key
    if let .ok constant := ident.getObjVal? "c" then
      names := names.push (← IO.ofExcept <| constant.getObjValAs? String "n").toName
  return names

/-- A name and each of its prefixes, for the parent lookups of rule 5. -/
partial def withPrefixes (name : Name) (into : NameSet) : NameSet :=
  if name.isAnonymous || into.contains name then into
  else withPrefixes name.getPrefix (into.insert name)

/-- The names that the module's constants refer to, other than its own constants. -/
def referencedNames (env : Environment) (own : NameSet) (infos : Array ConstantInfo)
    (mentioned : Array Name) : NameSet := Id.run do
  let mut found : NameSet := {}
  let mut wanted := mentioned
  for info in infos do
    wanted := wanted ++ info.type.getUsedConstants
    wanted := wanted ++ ((info.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
    if isStructure env info.name then
      wanted := wanted ++ (getStructureParentInfo env info.name).map (·.structName)
    if let some parent := tableParent? env info then wanted := wanted.push parent
  for name in wanted do
    found := withPrefixes name found
  -- The prefixes of the module's own constants, also without the private prefix, can be
  -- constants of other modules (rule 5).
  for info in infos do
    found := withPrefixes info.name.getPrefix found
    found := withPrefixes (privateToUserName info.name).getPrefix found
  return found.toArray.foldl (fun set name =>
    if own.contains name || !env.contains name then set else set.insert name) {}

/-- The facts of one module: imports, own constants with references, referenced constants, and
the `deriving instance` command of each instance that such a command declares. -/
def moduleJson (env : Environment) (module : Name) (ilean source : System.FilePath) : IO Json := do
  let some index := env.getModuleIdx? module
    | throw <| IO.userError s!"Module {module} was not loaded; build it before the extraction"
  let data := env.header.moduleData[index.toNat]!
  let infos := data.constNames.filterMap env.find?
  let own := data.constNames.foldl (·.insert ·) ({} : NameSet)
  let external := referencedNames env own infos (← ileanTargets ilean)
  let sortedInfos := infos.qsort (fun a b => a.name.toString < b.name.toString)
  let sortedExternal := external.toArray.qsort (fun a b => a.toString < b.toString)
  let instances := sortedInfos.filterMap fun info => do
    guard (Meta.isInstanceCore env info.name)
    let ranges ← rawRanges? env info.name
    return (info.name, ranges.selectionRange.pos)
  return Json.mkObj [
    ("module", toJson module.toString),
    ("imports", toJson (data.imports.map (·.module.toString) |>.qsort (· < ·))),
    ("constants", toJson (← sortedInfos.mapM (constantJson env · true))),
    ("external", toJson (← sortedExternal.filterMapM fun name => do
      let some info := env.find? name | return none
      return some (← constantJson env info false))),
    ("derivingCommands", ← derivingCommands env source instances)]

/-- Load one module with its imports and the states of the environment extensions, and write
its facts. The instance and class tables are extension states, so `loadExts` is needed. -/
unsafe def extractModule (module : Name) (source output : System.FilePath) : IO Unit := do
  let olean ← findOLean module
  let ilean := olean.withExtension "ilean"
  let env ← importModules #[{ module }] {} (loadExts := true) (level := .private)
  IO.FS.writeFile output (← moduleJson env module ilean source).compress

end LeanCodeStore
