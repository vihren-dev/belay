import Lean

set_option doc.verso true

/-! Export references from compiled declaration types and bodies for theorem exploration. -/

open Lean

namespace TheoremDependencies

/-- One explicitly selected compiled module and its supplied source file. -/
structure SelectedModule where
  /-- The exact Lean module name determines ownership of declarations. -/
  name : String
  /-- The source path supports navigation and source-hash checks. -/
  source : String
  /-- The package label groups modules without guessing from namespaces. -/
  package : String
  deriving FromJson, Inhabited

/-- Preserve every kernel declaration kind, including generated declarations. -/
def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Sort exact kernel names so repeated exports have identical bytes. -/
def referenceJson (names : Array Name) : Json :=
  toJson <| names.map Name.toString |>.qsort (· < ·)

/-- Preserve the declaration's own selection as zero-based UTF-16 coordinates. -/
def selectionJson (range : DeclarationRange) : Json :=
  toJson #[range.pos.line - 1, range.charUtf16, range.endPos.line - 1, range.endCharUtf16]

/-- Look up ownership through the compiled environment, including private names. -/
def owner? (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  return env.header.modules[index.toNat]!.module

/-- Keep type and body references separate; bodies include theorem and opaque values. -/
def declarationJson (env : Environment) (moduleName : Name) (info : ConstantInfo) : Json :=
  let body := info.value? (allowOpaque := true)
  let ranges := declRangeExt.find? (level := .server) env info.name
  Json.mkObj [
    ("name", toJson info.name.toString),
    ("displayName", toJson (privateToUserName info.name).toString),
    ("module", toJson moduleName.toString), ("kind", toJson (constantKind info)),
    ("private", toJson (isPrivateName info.name)),
    ("internal", toJson info.name.isInternalDetail),
    ("selection", ranges.map (selectionJson ·.selectionRange) |>.getD Json.null),
    ("bodyAvailable", toJson body.isSome),
    ("typeReferences", referenceJson info.type.getUsedConstants),
    ("bodyReferences", referenceJson <| body.map Expr.getUsedConstants |>.getD #[])]

/-- Reject incomplete or ambiguous selections before loading compiled modules. -/
def readSelection (path : System.FilePath) : IO (Array SelectedModule) := do
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let modules ← IO.ofExcept <| json.getObjValAs? (Array SelectedModule) "modules"
  if modules.isEmpty then
    throw <| IO.userError s!"Module manifest {path} is empty; select at least one compiled module"
  let mut seen : NameSet := {}
  for module in modules do
    if module.name.isEmpty || module.package.isEmpty || module.source.isEmpty then
      throw <| IO.userError s!"Module manifest {path} needs nonempty name, source and package fields"
    if seen.contains module.name.toName then
      throw <| IO.userError s!"Module {module.name} is selected twice in {path}; remove the duplicate"
    seen := seen.insert module.name.toName
    let source := System.FilePath.mk module.source
    if !(← source.pathExists) || (← source.isDir) then
      throw <| IO.userError s!"Source for module {module.name} is missing at {source}; supply its source file"
  return modules.qsort (·.name < ·.name)

/-- Add direct compiled imports and a supplied-source hash for optional proof-cost checks. -/
def moduleJson (env : Environment) (module : SelectedModule) : IO Json := do
  let some index := env.getModuleIdx? module.name.toName
    | throw <| IO.userError s!"Compiled module {module.name} was not loaded; build the selected module"
  let imports := env.header.moduleData[index.toNat]!.imports.map (·.module)
  let source ← IO.FS.readFile module.source
  return Json.mkObj [
    ("name", toJson module.name), ("source", toJson module.source),
    ("package", toJson module.package), ("imports", referenceJson imports),
    ("sourceHash", toJson (toString (hash source.crlfToLf)))]

/-- Import all selected artifacts with private data, retaining external edge targets as metadata. -/
def exportDependencies (modules : Array SelectedModule) : IO Json := do
  initSearchPath (← findSysroot)
  let imports := modules.map fun module => ({ module := module.name.toName } : Import)
  let env ← importModules imports {} (level := .private)
  let selected := modules.foldl (fun names module => names.insert module.name.toName) ({} : NameSet)
  let declarations := env.constants.toList.filterMap fun (_, info) => do
    let module ← owner? env info.name
    if selected.contains module then some (module, info) else none
  let declarations := declarations.toArray.qsort (fun a b => a.2.name.toString < b.2.name.toString)
  let mut external : NameSet := {}
  for (_, info) in declarations do
    let references := info.type.getUsedConstants ++
      ((info.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
    for name in references do
      let some owner := owner? env name
        | throw <| IO.userError s!"Reference {name} has no compiled owner; rebuild the selected modules"
      if !selected.contains owner then external := external.insert name
  let externalJson ← (external.toArray.qsort (fun a b => a.toString < b.toString)).mapM fun name => do
    let some info := env.find? name
      | throw <| IO.userError s!"Reference {name} is absent from the compiled environment; rebuild the selected modules"
    return Json.mkObj [
      ("name", toJson name.toString), ("module", toJson (owner? env name).get!.toString),
      ("kind", toJson (constantKind info))]
  return Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("leanVersion", toJson Lean.versionString),
    ("modules", toJson (← modules.mapM (moduleJson env))),
    ("declarations", toJson (declarations.map fun (module, info) => declarationJson env module info)),
    ("external", toJson externalJson)]

end TheoremDependencies

/-- Write the compiled dependency report for an explicit module manifest. -/
def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [manifest, output] =>
    let modules ← TheoremDependencies.readSelection manifest
    let report ← TheoremDependencies.exportDependencies modules
    IO.FS.writeFile output report.compress
    return 0
  | _ =>
    IO.eprintln "Theorem dependency export needs MANIFEST.json OUTPUT.json; select compiled modules in the manifest"
    return 2
