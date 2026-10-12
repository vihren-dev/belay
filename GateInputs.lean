import GateCore
import Belay.Sqlite.Codec.Resolution

/-! The generated inputs of a request, checked against the frontend's structural
record. Both gates resolve the record's schema and script again with the compiled
`resolveSchemaAndScript`, and require each generated declaration to equal the
result. A changed generated file therefore cannot change the target. See ADR 0008,
"Where resolution runs". -/

open Lean Belay.Sqlite

namespace ProofChecker

/-- Read and decode the frontend's structural record of the schema and script. -/
def readRecord (path : System.FilePath) : IO ScriptRecord := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept (decodeScriptRecord json)

/-- Resolve the record, or reject a record that the model does not describe. -/
def resolveRecord (record : ScriptRecord) : IO ResolvedScript :=
  match record.resolve with
  | .ok resolution => pure resolution
  | .error issue => throw <| IO.userError
      s!"the script record does not resolve: {(toJson issue).compress}; prepare the inputs again"

/-- The name, type and computed value of each declaration of {lit}`SchemaInputs`. -/
def schemaValues (resolution : ResolvedScript) : List (Name × Expr × Expr) :=
  let statements := mkApp (mkConst ``List [Level.zero]) (mkConst ``Syntax.Statement)
  [(`Generated.profile, mkConst ``Profile, toExpr resolution.profile),
   (`Generated.schema, statements, toExpr resolution.schema),
   (`Generated.startCatalog, mkConst ``Catalog, toExpr resolution.startCatalog)]

/-- The name, type and computed value of each declaration of {lit}`SqlInputs`. -/
def sqlValues (resolution : ResolvedScript) : List (Name × Expr × Expr) :=
  [(`Generated.script, mkApp (mkConst ``List [Level.zero]) (mkConst ``Syntax.Statement), toExpr resolution.script),
   (`Generated.resolved, mkApp (mkConst ``List [Level.zero]) (mkConst ``Resolved.Statement),
     toExpr resolution.resolved),
   (`Generated.nextCatalog, mkConst ``Catalog, toExpr resolution.nextCatalog)]

/-- Require each declaration to be a closed definition whose type and value are
definitionally equal to the given type and computed value. -/
def requireValues (env : Environment) (values : List (Name × Expr × Expr)) : IO Unit := do
  for (name, type, value) in values do
    let some info := env.toKernelEnv.find? name
      | throw <| IO.userError s!"missing generated declaration: {name}"
    let some body := info.value?
      | throw <| IO.userError s!"generated declaration is not a definition: {name}"
    unless info.levelParams.isEmpty do
      throw <| IO.userError s!"generated declaration has universe parameters: {name}"
    unless ← kernelResult (Kernel.isDefEq env {} info.type type) do
      throw <| IO.userError s!"generated declaration has another type: {name}"
    unless ← kernelResult (Kernel.isDefEq env {} body value) do
      throw <| IO.userError s!"generated declaration differs from the resolution of the script record: {name}"

end ProofChecker
