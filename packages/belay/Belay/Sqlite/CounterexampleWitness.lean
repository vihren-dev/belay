import Belay.Sqlite.CounterexampleCertificate
import Belay.Sqlite.DbBang
import Belay.Sqlite.Success

set_option doc.verso true

namespace Belay.Sqlite.Check

open Lean Meta

/-- The default complete environment for candidate search: a fixed 2025-01-01 clock and
new-connection counters. This is a candidate, not a restriction on {name}`Succeeds`.
Supply another {name}`Env` to check a different environment. -/
def candidateEnvironment : Env :=
  { Env.atTime 212602449600000 with counters := Counters.newConnection }

/-- Concrete terms supplied to witness search. Named inputs match quantified binder names;
the database and environment also match their types. A caller can instead supply any
selector directly to {lit}`refuteWith`, including witnesses of other Lean types. -/
structure Witness where
  /-- The database term, for example the elaboration of {lit}`db! "CREATE TABLE t(a)"`. -/
  database : Expr
  /-- A complete environment candidate. Use the default for a fixed clock and zero counters. -/
  environment : Expr := mkConst ``candidateEnvironment
  /-- Explicit inputs by quantified binder name, for example the value of {lit}`:amount`. -/
  named : Array (Name × Expr) := #[]

/-- Choose a supplied named input, database or environment for a quantified binder.
An unassigned binder is an error, rather than an assumed value. Named inputs take priority,
so a claim with several databases can supply a different term for each binder. -/
def Witness.choose (witness : Witness) (name : Name) (type : Expr) : MetaM Expr := do
  if let some (_, value) := witness.named.find? (·.1 == name) then return value
  if ← isDefEq type (mkConst ``Database) then return witness.database
  if ← isDefEq type (mkConst ``Env) then return witness.environment
  throwError "no SQL witness input for {name} : {type}; supply it by name"

/-- Apply a claimed universal fact to concrete inputs and checked preconditions until a
decidable false conclusion is reached. The fuel bounds the number of binders traversed.
This helper creates no evidence from sampling: each precondition and negated conclusion
passes {name}`decideCertified`. -/
private def contradictAt (choose : Name → Expr → MetaM Expr) (excluded : Array Name)
    (excludedLocals : Array FVarId) :
    Nat → Expr → MetaM Expr
  | 0, _ => throwError "SQL witness exhausted its binder budget"
  | fuel + 1, claimed => do
    let proposition ← inferType claimed
    -- Use a fixed-state decision instance before unfolding its interpreter in the elaborator.
    if !proposition.isForall then
      try
        return mkApp (← decideCertified (mkNot proposition) excluded excludedLocals) claimed
      catch _ => pure ()
    match ← whnf proposition with
    | .forallE name domain _ _ =>
      let input ← if ← isProp domain then decideCertified domain excluded excludedLocals else choose name domain
      checkWithKernel input
      contradictAt choose excluded excludedLocals fuel (mkApp claimed input)
    | _ =>
      let negation ← decideCertified (mkNot proposition) excluded excludedLocals
      return mkApp negation claimed

/-- Refute a proposition by instantiating its universal binders with a caller's selector.
Every implication premise must be decidable and true at those inputs; the resulting
conclusion must be decidable and false. The complete refutation is kernel checked and
audited, so unsupported propositions and invalid candidates throw without proving anything.
Use {lit}`refuteWitness` for the database/environment convenience record. -/
def refuteWith (proposition : Expr) (choose : Name → Expr → MetaM Expr)
    (excluded : Array Name := #[]) (excludedLocals : Array FVarId := #[])
    (binderBudget : Nat := 64) : MetaM Expr := do
  let proof ← withLocalDeclD `claimed proposition fun claimed => do
    mkLambdaFVars #[claimed] (← contradictAt choose excluded excludedLocals binderBudget claimed)
  certify (mkNot proposition) proof excluded excludedLocals

/-- Check every supplied witness term, including the required database and environment types,
then refute the claim with those inputs.
An invalid or admitted database is rejected even if the particular claim does not use it.
The arbitrary selector primitive {name}`refuteWith` remains available for other inputs. -/
def refuteWitness (proposition : Expr) (witness : Witness)
    (excluded : Array Name := #[]) (excludedLocals : Array FVarId := #[])
    (binderBudget : Nat := 64) : MetaM Expr := do
  let inputs := #[witness.database, witness.environment] ++ witness.named.map (·.2)
  auditDependencies inputs excluded excludedLocals
  checkWithKernel (mkApp2 (mkConst ``id [Level.one]) (mkConst ``Database) witness.database)
  checkWithKernel (mkApp2 (mkConst ``id [Level.one]) (mkConst ``Env) witness.environment)
  witness.named.forM (fun (_, input) => checkWithKernel input)
  refuteWith proposition witness.choose excluded excludedLocals binderBudget

end Belay.Sqlite.Check
