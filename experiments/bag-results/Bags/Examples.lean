import Bags.Sample

/-!
# Decidable bag equality on small examples

Equality of bags of a type with decidable equality is decidable through `List.isPerm`. The
kernel evaluates it directly, so `decide +kernel` settles equalities of literal bags. For a type
with a sort order, the sample gives a second decision: the kernel sorts both bags and compares
the sorted lists.
-/

open BagResults

example : Bag.ofList [1, 2, 3] = Bag.ofList [3, 1, 2] := by decide +kernel
example : Bag.ofList [1, 2, 3] ≠ Bag.ofList [3, 1, 1] := by decide +kernel
example : Bag.ofList [1, 2, 3] = Bag.ofList [3, 1, 2] := by decide
example : Bag.ofList (List.range 40) = Bag.ofList (List.range 40).reverse := by decide +kernel

/-- The order of natural numbers as a sort order. -/
def natOrder : SortOrder Nat where
  le a b := decide (a ≤ b)
  total a b := by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  trans a b c := by simp only [decide_eq_true_eq]; omega
  antisymm a b := by simp only [decide_eq_true_eq]; omega

example : (Bag.ofList [3, 1, 2, 1]).sample natOrder = [1, 1, 2, 3] := by decide +kernel
example : Bag.ofList [1, 2, 3] = Bag.ofList [3, 1, 2] := (Bag.sample_eq_iff natOrder _ _).mp rfl

section
/-- The sample decision for bags of natural numbers, tried before the generic decision. -/
local instance (priority := high) natBagDecEq : DecidableEq (Bag Nat) := Bag.decEqBySample natOrder
example : Bag.ofList (List.range 40) = Bag.ofList (List.range 40).reverse := by decide +kernel
end
