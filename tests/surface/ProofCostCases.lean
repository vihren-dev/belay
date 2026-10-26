import ProofCostCollector

/-! Coverage of the proposed body-elaboration boundary. The generated declarations
are intentionally inventoried as well as the declarations that receive traces. -/
namespace Coverage

/-- Tactic elaboration proves truth. -/
theorem tactic : True := by trivial

/-- Term elaboration proves truth. -/
theorem term : True := True.intro

/-- A definition whose value is a proof of truth. -/
def proofDefinition : True := True.intro

/-- A predicate that always holds, with a proposition as its value. -/
def predicate : Prop := True

example : True := True.intro
example : True := by trivial

/-- Private names retain the module component of Lean's generated identity. -/
private theorem hidden : True := True.intro

/-- This proof is part of a value-producing declaration, with a generated proof helper. -/
def embedded : { n : Nat // n = n } := ⟨1, rfl⟩

/-- Recursive elaboration generates auxiliaries without separate body records. -/
theorem recursive : ∀ n : Nat, n = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (recursive n)

#print axioms tactic
#print axioms term
#print axioms proofDefinition
#print axioms predicate
#print axioms hidden
#print axioms embedded
#print axioms recursive
end Coverage

#proof_cost_records
#proof_cost_commands
#proof_cost_snapshot
