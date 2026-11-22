import Lean

/-! Facts about one compiled constant that the folding rules of the Lean code store read.

The specification of the store (`docs/records/spec-lean-code-store.md`, "Generated
constants") decides from these facts if a constant is a written declaration or a generated
constant, and which declaration is its parent. This file only reads the compiled
environment; the Python side applies the rules. -/

open Lean

namespace LeanCodeStore

/-- The kernel kind of a constant, before the structure, class and instance tables replace it. -/
def kernelKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- The module that declares a constant, through the compiled environment. -/
def owner? (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  return env.header.modules[index.toNat]!.module

/-- A range as `[line, column, utf16Column, endLine, endColumn, endUtf16Column]`, lines from 1.

Columns in code points cut the source text; UTF-16 columns compare with `.ilean` positions. -/
def rangeJson (range : DeclarationRange) : Json :=
  toJson #[range.pos.line, range.pos.column, range.charUtf16,
    range.endPos.line, range.endPos.column, range.endCharUtf16]

/-- The raw declaration ranges of a constant, without the redirect of `findDeclarationRanges?`.

That function gives an auxiliary recursor the range of its type; rule 1 must see that the
recursor itself has no range. -/
def rawRanges? (env : Environment) (name : Name) : Option DeclarationRanges :=
  declRangeExt.find? (level := .exported) env name <|> declRangeExt.find? (level := .server) env name

/-- The type that Lean's inductive, auxiliary-recursor and projection tables give as the source
of a constant (rule 1), when such a table has the constant. -/
def tableParent? (env : Environment) (info : ConstantInfo) : Option Name :=
  match info with
  | .ctorInfo value => some value.induct
  | .recInfo _ => some info.name.getPrefix
  | .inductInfo _ | .quotInfo _ | .axiomInfo _ => none
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
    if isAuxRecursor env info.name || isNoConfusion env info.name then some info.name.getPrefix
    else do
      let projection ← env.getProjectionFnInfo? info.name
      match env.find? projection.ctorName with
      | some (.ctorInfo value) => some value.induct
      | _ => none

/-- The head constant of the conclusion of an instance type: the class of the instance. -/
def instanceClass? (type : Expr) : Option Name :=
  type.getForallBody.getAppFn.constName?

/-- Sorted names of a reference list, each with its declaring module. -/
def referencesJson (env : Environment) (names : Array Name) : Json :=
  let sorted := names.qsort (fun a b => a.toString < b.toString)
  toJson <| sorted.map fun name =>
    #[toJson name.toString, toJson ((owner? env name).map Name.toString |>.getD "")]

/-- Whether Lean's own `isAutoDeclOrPrivate_Internal` calls the constant generated.

The prototype records it next to the rules of the specification to compare the two. -/
def leanAutoDecl (env : Environment) (name : Name) : IO Bool := do
  let context : Core.Context := { fileName := "<extractor>", fileMap := default }
  let (result, _) ← (isAutoDeclOrPrivate_Internal name).toIO context { env }
  return result

/-- All facts of one constant. With `withReferences`, also its type and body references. -/
def constantJson (env : Environment) (info : ConstantInfo) (withReferences : Bool) : IO Json := do
  let name := info.name
  let ranges := rawRanges? env name
  let parents := if isStructure env name then
    (getStructureParentInfo env name).map (·.structName) else #[]
  let isInstance := Meta.isInstanceCore env name
  let mut fields : List (String × Json) := [
    ("name", toJson name.toString),
    ("module", toJson ((owner? env name).map Name.toString |>.getD "")),
    ("kernelKind", toJson (kernelKind info)),
    ("range", ranges.map (rangeJson ·.range) |>.getD Json.null),
    ("selection", ranges.map (rangeJson ·.selectionRange) |>.getD Json.null),
    ("tableParent", toJson ((tableParent? env info).map Name.toString)),
    ("structure", toJson (isStructure env name)), ("class", toJson (isClass env name)),
    ("instance", toJson isInstance),
    ("instanceClass", toJson (if isInstance then (instanceClass? info.type).map Name.toString else none)),
    ("parents", referencesJson env parents),
    ("matcher", toJson (Meta.isMatcherCore env name)),
    ("reserved", toJson (isReservedName env name)),
    ("leanAutoDecl", toJson (← leanAutoDecl env name))]
  if withReferences then
    let body := (info.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]
    fields := fields ++ [("type", referencesJson env info.type.getUsedConstants),
      ("body", referencesJson env body)]
  return Json.mkObj fields

end LeanCodeStore
