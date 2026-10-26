import Lean.Meta.Check
import Lean.Meta.CollectFVars
import Lean.Meta.AppBuilder

set_option doc.verso true

/-! The trust boundary for SQL checks. Search supplies expressions; this module checks their
types with Lean's kernel and audits their dependencies before any result is reported. -/

namespace Belay.Sqlite.Check

open Lean Meta

/-- The logical axioms accepted by SQL certificates. User axioms and compiler-trust axioms
are excluded; {name}`propext`, {name}`Classical.choice` and {name}`Quot.sound` are permitted. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Lean's generated native-decision declaration prefix. A matching name component is
excluded from checked SQL evidence even when it appears through another declaration. -/
def nativeDecisionPrefix : String := "_native"

/-- Names that cannot justify a checked result: admitted proofs, native decision axioms and
declarations the caller excludes, such as the theorem currently being checked. -/
def forbiddenDependency (excluded : Array Name) (name : Name) : Bool :=
  excluded.contains name || name == ``sorryAx || name == ``Lean.ofReduceBool ||
    (name.toString.splitOn ".").any (·.startsWith nativeDecisionPrefix)

/-- Audit types and bodies transitively, including the types and values of used local
variables. The caller can exclude a theorem and local assumptions. User axioms are rejected;
only Lean's logical axioms are allowed. Kernel checking separately rejects unsafe declarations.
Use empty exclusions for an explicit witness outside automatic theorem checking. -/
def auditDependencies (expressions : Array Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : MetaM Unit := do
  let mut pending := expressions
  let mut seen : NameSet := {}
  let mut locals : FVarIdSet := {}
  while !pending.isEmpty do
    checkSystem "SQL certificate dependencies"
    let expression := pending.back!
    pending := pending.pop
    if expression.hasMVar then
      throwError "SQL certificate contains an unresolved metavariable"
    for name in expression.getUsedConstants do
      if forbiddenDependency excluded name then
        throwError "SQL certificate depends on excluded declaration {name}"
      if !seen.contains name then
        seen := seen.insert name
        let info ← getConstInfo name
        if info.isAxiom && !allowedAxioms.contains name then
          throwError "SQL certificate depends on axiom {name}"
        pending := pending.push info.type
        if let some value := info.value? (allowOpaque := true) then
          pending := pending.push value
    for id in (Lean.collectFVars {} expression).fvarIds do
      if excludedLocals.contains id then
        throwError "SQL certificate depends on an excluded local assumption"
      if !locals.contains id then
        locals := locals.insert id
        let declaration ← id.getDecl
        pending := pending.push declaration.type
        if let some value := declaration.value? then
          pending := pending.push value

/-- Check that the supplied expression proves exactly the supplied proposition in the
current local context, then audit all dependencies with {name}`auditDependencies`.
The kernel checks an application of {name}`id` at the expected proposition, so a searcher
cannot substitute a proof of another claim. No declaration is added to the environment.
Use this primitive to certify proofs from a custom candidate generator. -/
def certify (proposition proof : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : MetaM Expr := do
  let proposition ← instantiateMVars proposition
  let proof ← instantiateMVars proof
  unless ← isProp proposition do
    throwError "SQL certification expects a proposition"
  auditDependencies #[proposition, proof] excluded excludedLocals
  checkWithKernel (mkApp2 (mkConst ``id [Level.zero]) proposition proof)
  return proof

/-- Construct a decision proof and certify it in the kernel. A false proposition, missing
decision procedure or exhausted elaboration budget throws an exception; none is evidence
for the proposition. For example, this primitive can prove a concrete query observation. -/
def decideCertified (proposition : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : MetaM Expr := do
  let (reduced, decision) ← try
      pure (proposition, ← synthInstance (mkApp (mkConst ``Decidable) proposition))
    catch _ =>
      let reduced ← whnf proposition
      pure (reduced, ← synthInstance (mkApp (mkConst ``Decidable) reduced))
  let trueRefl := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
  certify proposition (mkApp3 (mkConst ``of_decide_eq_true) reduced decision trueRefl) excluded excludedLocals

end Belay.Sqlite.Check
