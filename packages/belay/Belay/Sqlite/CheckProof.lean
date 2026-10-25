import Lean.Elab.Tactic.Basic
import Belay.Sqlite.CounterexampleCertificate
import Belay.Sqlite.CheckBudget
import Belay.Sqlite.SqlSimpLaws

set_option doc.verso true

/-! Available checked proof automation, before S6 supplies {lit}`sql_auto`. The tactic's claim of
success is insufficient: the resulting term must prove the original proposition in the kernel
and pass the same dependency exclusions as counterexamples. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term Tactic

/-- A proposed proof term and tactic script. The checking operations certify the term and
independently elaborate the script against the original proposition. Constructing this record
alone establishes neither claim; use {name}`certify` for a term without a tactic suggestion. -/
structure Proven where
  /-- The proposed term, certified against the original proposition before acceptance. -/
  proof : Expr
  /-- The proposed script, independently checked before a successful editor suggestion. -/
  tactic : Syntax

/-- Remove quotation scopes before printing a suggested script. The returned syntax is an
untrusted text proposal: callers must parse it and certify its proof against the original goal. -/
def printableScript (script : Syntax) : Syntax :=
  script.rewriteBottomUp fun node =>
    if node.isIdent then mkIdentFrom node node.getId.eraseMacroScopes else node

/-- Run caller-selected proof automation on the exact proposition, without error-to-sorry
recovery. An error diagnostic, unsolved goal or forbidden dependency rejects the attempt. Use this primitive
to supply richer automation without changing the candidate search or certification rules. -/
def proveWith (proposition : Expr) (tactic : Syntax) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM Proven := withoutErrToSorry do
  let priorErrors := (← getThe Core.State).messages.reportedPlusUnreported.toList.filter (·.severity == .error) |>.length
  let goal ← mkFreshExprMVar proposition
  let remaining ← Tactic.run goal.mvarId! (evalTactic tactic)
  let errors := (← getThe Core.State).messages.reportedPlusUnreported.toList.filter (·.severity == .error) |>.length
  if errors > priorErrors then throwError "SQL proof search emitted an error"
  unless remaining.isEmpty do throwError "SQL proof search left unresolved goals"
  let proof ← certify proposition (← instantiateMVars goal) excluded excludedLocals
  return { proof, tactic }

/-- Try the existing logical, SQL simp-set and kernel-decision primitives. This is a bounded
attempt, not the future S6 {lit}`sql_auto` tactic. Failed automation supplies no evidence for P. -/
def tryProof (proposition : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM (Option Proven) := do
  let tactic ← `(tactic| (intros; first | rfl | trivial | (simp [sql_simp]; done) | decide +kernel))
  attempt (proveWith proposition tactic excluded excludedLocals)

end Belay.Sqlite.Check
