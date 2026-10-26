import Belay.Sqlite.ProofCost
import ProofCostReader

/-! Coverage of the proof-cost collector: each kind of declaration that the record set must
include, and each that it must leave out. The comment before a declaration says which. -/

/-- A macro that expands to a theorem, which Lean elaborates through a nested command. -/
macro "macro_theorem " name:ident : command => `(theorem $name : True := by trivial)

set_option belay.proofCosts true

namespace Coverage

/-- Measured: a theorem proved by tactics. -/
theorem tactic : True := by trivial

/-- Measured: a theorem proved by a term. -/
theorem term : True := True.intro

/-- Measured: a definition whose value is a proof. -/
def proofDefinition : True := True.intro

/-- Not measured: a definition of a proposition is not a proof. -/
def predicate : Prop := True

/-- Not measured: a definition of data. -/
def plain : Nat := 1

/-- Measured as anonymous examples. -/
example : True := True.intro
example : True := by trivial

/-- Measured with a private identity. -/
private theorem hidden : True := True.intro

/-- Not measured: the proof inside the value belongs to no separate record. -/
def embedded : { n : Nat // n = n } := ⟨1, rfl⟩

/-- Measured once for the whole recursive proof; helpers get no record. -/
theorem recursive : ∀ n : Nat, n = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (recursive n)

/-- Measured once, with the proof in the {lit}`where` clause. -/
theorem withWhere : True := helper
where
  helper : True := by trivial

macro_theorem fromMacro

mutual
/-- Measured: the first peer of a mutual block. -/
theorem evenPeer : ∀ n : Nat, n = n ∧ True
  | 0 => ⟨rfl, trivial⟩
  | n + 1 => ⟨rfl, (oddPeer n).2⟩
/-- Measured: the second peer of a mutual block. -/
theorem oddPeer : ∀ n : Nat, n = n ∧ True
  | 0 => ⟨rfl, trivial⟩
  | n + 1 => ⟨rfl, (evenPeer n).2⟩
end

mutual
/-- Measured: a proof-valued definition in a mutual block. -/
def mutualProofOne : True := trivial
/-- Not measured: a definition of data in the same block. -/
def mutualData : Nat := 2
/-- Measured: another proof-valued definition in the same block. -/
def mutualProofTwo : True := trivial
end

end Coverage

set_option belay.proofCosts false

/-- Not measured: the option is off in this part of the file. -/
theorem unmeasured : True := by trivial

#print axioms Coverage.tactic
#print axioms Coverage.recursive
#print axioms Coverage.evenPeer
#proof_cost_records
#proof_cost_snapshot
