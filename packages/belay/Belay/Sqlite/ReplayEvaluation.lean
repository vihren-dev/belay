import Belay.Sqlite.CounterexampleCertificate
import Belay.Sqlite.EvalDatabase
import Belay.Sqlite.Script
import Belay.Sqlite.Model.Codec.Resolution

set_option doc.verso true

/-! Evaluation used only to prepare replay data. Compiled evaluation is untrusted: the kernel
must confirm that the reified result is equal to the original script or database projection.
This also rejects a custom compiled implementation that disagrees with its Lean definition. -/

namespace Belay.Sqlite.Replay

open Lean Elab Term Meta

/-- Evaluate a script through Lean's compiled implementation. Only the checked wrapper
below can use the result as replay data for a supplied expression. -/
unsafe def evaluateScriptUnsafe (expression : Expr) : TermElabM Script :=
  evalExpr Script (mkConst ``Script) expression

/-- Compiled script evaluation, before equality with the original term has been checked. -/
@[implemented_by evaluateScriptUnsafe]
opaque evaluateScript (expression : Expr) : TermElabM Script

/-- Kernel-check equality of a projected value with its reified compiled result. Exclusions
are the same ones used for the original claim's certificate. -/
private def checkValue (expression projection literal : Expr) (excluded : Array Name)
    (excludedLocals : Array FVarId) : TermElabM Unit := do
  discard <| Check.certify (← mkEq (mkApp projection expression) literal)
    (← mkEqRefl literal) excluded excludedLocals

/-- Evaluate a database for replay and check its exact raw catalog, rowids and values against
the original expression. Runtime validity alone cannot establish that equality. -/
def databaseValue (expression : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM Database := do
  Check.auditDependencies #[expression] excluded excludedLocals
  checkWithKernel (mkApp2 (mkConst ``id [Level.one]) (mkConst ``Database) expression)
  let value ← evaluateDatabaseExpr expression
  checkValue expression (mkConst ``Database.raw) (toExpr value.raw) excluded excludedLocals
  return value

/-- Evaluate a script for replay and check its exact statements and bindings against the
original expression. Source metadata cannot replace this check. -/
def scriptValue (expression : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM Script := do
  Check.auditDependencies #[expression] excluded excludedLocals
  checkWithKernel (mkApp2 (mkConst ``id [Level.one]) (mkConst ``Script) expression)
  let value ← evaluateScript expression
  checkValue expression (mkConst ``Script.statements) (toExpr value.statements) excluded excludedLocals
  return value

end Belay.Sqlite.Replay
