import Belay.Sqlite.CounterexampleWitness
import Belay.Sqlite.CheckCompiled

set_option doc.verso true

/-! The compiled screen of a claim. The search runs it on many candidate databases and certifies
only the candidates that it accepts. The screen only proposes: certification in the kernel
decides each result, so a wrong screen can waste time or miss a counterexample, and cannot give
a wrong result. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term

/-- A screen: true when a database and a value of the value pool, with the other inputs of the
check, satisfy every premise of the claim and falsify its conclusion. The value goes to each
quantified {name}`Value` input that has no supplied value. -/
abbrev Screen := Database → Value → Bool

/-- A Boolean term that is true when two values differ in a decidable field, as
{name}`refuteDifference` finds such a field: the inequality when it is decidable, else any field
of a structure, to the given depth. It throws when no field is decidable. -/
def differenceTerm : Nat → Expr → Expr → MetaM Expr
  | 0, _, _ => throwError "the values do not differ in a decidable field within the nesting limit"
  | depth + 1, left, right => do
    try return ← mkDecide (mkNot (← mkEq left right)) catch _ => pure ()
    let type ← whnf (← inferType left)
    let some structureName := type.getAppFn.constName?
      | throwError "the values have no decision procedure and are no structure"
    unless isStructure (← getEnv) structureName do
      throwError "the values have no decision procedure and are no structure"
    let mut parts := #[]
    for field in getStructureFields (← getEnv) structureName do
      try parts := parts.push (← differenceTerm depth (← mkProjection left field) (← mkProjection right field))
      catch _ => pure ()
    let some first := parts[0]? | throwError "the values do not differ in a decidable field"
    parts[1:].foldlM (fun found part => mkAppM ``or #[found, part]) first

/-- The Boolean term of a screen for a proposition, as {lit}`contradictAt` refutes it: a premise
becomes a {name}`dite` on its decision, so that later binders can use its proof; an input comes
from the selector; the conclusion must be false. An equivalence of programs compares its actual
runs ({name}`refuteByActualRun?`). The fuel bounds the binders. -/
def screenBody (choose : Name → Expr → MetaM Expr) : Nat → Expr → MetaM Expr
  | 0, _ => throwError "the claim has more binders than the screen follows"
  | fuel + 1, proposition => do
    if !proposition.isForall then
      try return ← mkDecide (mkNot proposition) catch _ => pure ()
      if programRelationNames.any proposition.getAppFn.isConstOf then
        return ← withLocalDeclD `claimed proposition fun claimed => do
          let actual ← mkAppM ``observationProfile_actual #[claimed]
          let some (_, left, right) := (← inferType actual).eq?
            | throwError "the actual runs of this relation cannot be compared"
          if left.containsFVar claimed.fvarId! || right.containsFVar claimed.fvarId! then
            throwError "the actual runs of this relation cannot be compared"
          differenceTerm actualRunNesting left right
    match ← whnf proposition with
    | .forallE name domain body _ =>
      if ← isProp domain then
        let decision ← try synthInstance (mkApp (mkConst ``Decidable) domain)
          catch _ => synthInstance (mkApp (mkConst ``Decidable) (← whnf domain))
        let accepted ← withLocalDeclD name domain fun premise => do
          mkLambdaFVars #[premise] (← screenBody choose fuel (body.instantiate1 premise))
        let rejected ← withLocalDeclD name (mkNot domain) fun premise =>
          mkLambdaFVars #[premise] (mkConst ``false)
        return mkApp5 (mkConst ``dite [1]) (mkConst ``Bool) domain decision accepted rejected
      else screenBody choose fuel (body.instantiate1 (← choose name domain))
    | conclusion => mkDecide (mkNot conclusion)

/-- The closed term of the screen ({name}`Screen`) of a claim, for the environment and the
supplied named inputs of the check. A database binder gets the screen's database, a context the
initial context of that database and the environment, and a {name}`Value` binder without a
supplied value the screen's value. Another binder without a supplied value has no screen. -/
def screenTerm (proposition environment : Expr) (named : Array (Name × Expr)) (fuel : Nat := 64) :
    MetaM Expr :=
  withLocalDeclD `database (mkConst ``Database) fun database =>
    withLocalDeclD `value (mkConst ``Value) fun value => do
      let choose (name : Name) (type : Expr) : MetaM Expr := do
        if let some (_, input) := named.find? (·.1 == name) then return input
        if ← isDefEq type (mkConst ``Database) then return database
        if ← isDefEq type (mkConst ``Env) then return environment
        if ← isDefEq type (mkConst ``ExecutionContext) then
          return mkApp2 (mkConst ``ExecutionContext.initial) database environment
        if ← isDefEq type (mkConst ``Value) then return value
        throwError "the screen has no input for {name} : {type}"
      let body ← instantiateMVars (← screenBody choose fuel proposition)
      mkLambdaFVars #[database, value] body

/-- Build and compile the screen of a claim ({name}`screenTerm`), after the closure check of
compiled code ({name}`checkCompiledClosure`). It throws when the claim has no screen. -/
def compileScreen (proposition environment : Expr) (named : Array (Name × Expr)) : TermElabM Screen := do
  let term ← screenTerm proposition environment named
  checkCompiledClosure term
  let type ← mkArrow (Lean.mkConst ``Database) (← mkArrow (Lean.mkConst ``Value) (Lean.mkConst ``Bool))
  compileTerm Screen type term

/-- The position of the first candidate from {lit}`start` that the screen accepts with the value,
among at most {lit}`count` candidates. -/
def firstAccepted (screen : Screen) (value : Value) (candidates : Array Database) (start count : Nat) :
    Option Nat :=
  (List.range' start (min count (candidates.size - start))).find? fun position =>
    candidates[position]?.any (screen · value)

end Belay.Sqlite.Check
