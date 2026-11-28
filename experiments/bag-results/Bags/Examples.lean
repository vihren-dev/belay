import Bags.Bag

/-!
# Decidable bag equality on small examples

Equality of bags of a type with decidable equality is decidable through `List.isPerm`. The
kernel evaluates it directly, so `decide +kernel` settles equalities of literal bags.
-/

open BagResults

example : Bag.ofList [1, 2, 3] = Bag.ofList [3, 1, 2] := by decide +kernel
example : Bag.ofList [1, 2, 3] ≠ Bag.ofList [3, 1, 1] := by decide +kernel
example : Bag.ofList [1, 2, 3] = Bag.ofList [3, 1, 2] := by decide
example : Bag.ofList (List.range 40) = Bag.ofList (List.range 40).reverse := by decide +kernel
