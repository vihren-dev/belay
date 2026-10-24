import Belay.Sqlite.CounterexampleWitness

set_option doc.verso true

/-! A finite shrink loop at the certificate boundary. Every retained proposal must refute
the original proposition, including proposals from user-supplied shrinkers. -/

namespace Belay.Sqlite.Check

open Lean Meta

/-- Certify the initial witness, then try at most the supplied number of shrink proposals.
A proposal is retained only after refuting the same original proposition in the kernel;
rejected proposals keep the previous witness and proof. The first accepted proposal starts
another shrink round. The bound applies to all attempts, including invalid and repeated
proposals, so even a custom shrinker that returns its input terminates. Use zero attempts
to certify the original witness unchanged. Cancellation and elaboration budgets propagate. -/
def shrinkCertified (proposition : Expr) (initial : Witness)
    (proposals : Witness → MetaM (List Witness)) (attempts : Nat := 32)
    (excluded : Array Name := #[]) (excludedLocals : Array FVarId := #[]) : MetaM (Witness × Expr) := do
  let proof ← refuteWitness proposition initial excluded excludedLocals
  if attempts == 0 then return (initial, proof)
  loop attempts initial proof (← proposals initial)
where
  /-- Consume one attempt per candidate, preserving the last certified witness on failure. -/
  loop : Nat → Witness → Expr → List Witness → MetaM (Witness × Expr)
    | 0, witness, proof, _ => pure (witness, proof)
    | _, witness, proof, [] => pure (witness, proof)
    | fuel + 1, witness, proof, candidate :: remaining => do
      checkSystem "SQL counterexample shrinking"
      let certified ← try
          pure (some (← refuteWitness proposition candidate excluded excludedLocals))
        catch _ => pure none
      match certified with
      | some certificate =>
        if fuel == 0 then return (candidate, certificate)
        loop fuel candidate certificate (← proposals candidate)
      | none => loop fuel witness proof remaining

end Belay.Sqlite.Check
