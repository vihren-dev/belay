import Lean.Meta.Reduce
import Lean.Meta.CtorRecognizer
import Belay.Sqlite.CheckBudget
import Belay.Sqlite.ReplayEvaluation

set_option doc.verso true

/-! Cooperative evaluation for background SQL checks. Lean reduces computations under its
heartbeat and cancellation checks. Native decoding receives only finite constructor data;
all reported values are still checked against the original expression. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term

/-- Reduce data with Lean's metaprogram evaluator at full transparency, then reject residual
computation or values beyond {name}`maxDataNodes` or {name}`maxLiteralBytes`. Types and proofs
are erased by decoding and need no data traversal.
Full transparency evaluates ordinary well-founded helpers such as the SQL hint collector.
Opaque computations, functions and oversized data leave the background check inconclusive;
explicit witness certification remains available independently. -/
def normalizedData (expression : Expr) : MetaM Expr := do
  let value ← withTransparency .all <| reduce expression (explicitOnly := false)
  let mut pending := #[value]
  let mut literalBytes := 0
  for _ in List.range maxDataNodes do
    if pending.isEmpty then return value
    checkSystem "SQL literal normalization"
    let current := pending.back!
    pending := pending.pop
    if (← isType current) || (← isProof current) then continue
    match current with
    | .mdata _ body => pending := pending.push body
    | .lit literal =>
      literalBytes := literalBytes + match literal with
        | .strVal text => text.utf8ByteSize
        | .natVal number => number.log2 / 8 + 1
      if literalBytes > maxLiteralBytes then throwError "SQL checking reached its literal byte limit"
    | _ =>
      unless (← isConstructorAppCore? current).isSome do
        throwError "SQL checking could not reduce this value to literal data"
      pending := pending ++ current.getAppArgs
  throwError "SQL checking reached its literal data limit"

/-- Decode an already normalized expression. Its result is untrusted until the caller checks
its equality with the original expression; use the checked wrapper below. -/
private unsafe def decodeUnsafe (α : Type) [ToExpr α] (expression : Expr) : TermElabM α :=
  evalExpr α (toTypeExpr α) expression

/-- Native decoding is restricted to finite constructor data by the checked wrapper. -/
@[implemented_by decodeUnsafe]
private opaque decode (α : Type) [ToExpr α] (expression : Expr) : TermElabM α

/-- Evaluate finite data cooperatively and kernel-check equality with the original expression.
Use this for owned sampling, shrinking and model-observation computations. A compiled override
cannot change the original expression's meaning, because computation finishes before decoding. -/
def dataValue (α : Type) [ToExpr α] (expression : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM α := do
  auditDependencies #[expression] excluded excludedLocals
  let value ← decode α (← normalizedData expression)
  discard <| certify (← mkEq expression (toExpr value)) (← mkEqRefl (toExpr value)) excluded excludedLocals
  return value

/-- Obtain a database through cooperative normalization and constructor-only decoding.
Its exact raw catalog and rows are checked against the original term. Use the explicit
witness primitive when the background data limit is too small for a supplied database. -/
def databaseValue (expression : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM Database := do
  auditDependencies #[expression] excluded excludedLocals
  checkWithKernel (mkApp2 (mkConst ``id [Level.one]) (mkConst ``Database) expression)
  let value ← evaluateDatabaseExpr (← normalizedData expression)
  let projection := mkApp (mkConst ``Database.raw) expression
  discard <| certify (← mkEq projection (toExpr value.raw))
    (← mkEqRefl (toExpr value.raw)) excluded excludedLocals
  return value

/-- Obtain a script through cooperative normalization and constructor-only decoding, retaining
its actual bindings. Equality is checked against the supplied statement projection; source
annotations only recover the text later. -/
def scriptValue (expression : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM Script := do
  let statements ← dataValue (List (Model.Syntax.Statement × List Value))
    (mkApp (mkConst ``Script.statements) expression) excluded excludedLocals
  return ⟨statements⟩

end Belay.Sqlite.Check
