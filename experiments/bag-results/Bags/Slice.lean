import Bags.Choice
import Bags.Ranked

/-!
# OFFSET and LIMIT on lists

`slice skip keep l` is the part of a list that OFFSET `skip` and LIMIT `keep` take. This file
also shows that the lists of a sub-bag of size `j` are exactly the middle slices of length `j`
of the arrangements of the bag (`take_bind_arrange`).
-/

namespace BagResults

variable {α : Type}

/-- The rows of a list that OFFSET `skip` and LIMIT `keep` take. `none` is no LIMIT. -/
def slice (skip : Nat) : Option Nat → List α → List α
  | none, l => l.drop skip
  | some n, l => (l.drop skip).take n

/-- For each window and all lists `l` and `m`: if `l` has at most `skip` rows, then the slice
of `l ++ m` is the slice of `m` with `skip - l.length` rows skipped. -/
theorem slice_append_of_length_le (skip : Nat) (keep : Option Nat) {l : List α} (m : List α)
    (h : l.length ≤ skip) : slice skip keep (l ++ m) = slice (skip - l.length) keep m := by
  have d : (l ++ m).drop skip = m.drop (skip - l.length) := by
    rw [List.drop_append, List.drop_of_length_le h, List.nil_append]
  cases keep <;> simp only [slice, d]

/-- For each offset `skip` and all lists `l` and `m`: if `l` has at least `skip` rows, then
OFFSET `skip` without LIMIT on `l ++ m` is the last `l.length - skip` rows of `l`, then `m`. -/
theorem slice_none_append (skip : Nat) {l : List α} (m : List α) (h : skip ≤ l.length) :
    slice skip none (l ++ m) = (l.drop skip).take (l.length - skip) ++ m := by
  rw [slice, List.drop_append_of_le_length h, List.take_of_length_le (by simp)]

/-- For each offset `skip`, limit `k` and all lists `l` and `m`: if `l` has at least `skip`
rows, then the slice of `l ++ m` is a slice of `l` with `j = min k (l.length - skip)` rows,
then the first `k - j` rows of `m`. -/
theorem slice_some_append (skip k : Nat) {l : List α} (m : List α) (h : skip ≤ l.length) :
    slice skip (some k) (l ++ m) = (l.drop skip).take (min k (l.length - skip)) ++
      slice 0 (some (k - min k (l.length - skip))) m := by
  simp only [slice, List.drop_append_of_le_length h, List.take_append, List.drop_zero,
    List.length_drop]
  congr 1
  · exact List.take_eq_take_iff.mpr (by simp only [List.length_drop]; omega)
  · congr 1; omega

namespace Bag

/-- For each bag `g` and all numbers `skip` and `j` with `skip + j ≤ card g`: a list `l₁` is
an arrangement of a possible result of LIMIT `j` on `g` if and only if `l₁` is the slice of
`j` rows after `skip` rows of an arrangement of `g`.
Proof sketch: from a list `l₁` of a sub-bag, build an arrangement of `g` that has `skip`
other rows, then `l₁`, then the remaining rows. Conversely, a middle slice of an arrangement
is the start of the arrangement that moves the slice to the front. -/
theorem take_bind_arrange (g : Bag α) (skip j : Nat) (fits : skip + j ≤ g.card)
    (l₁ : List α) :
    (g.take j >>= Bag.arrange) l₁ ↔ ∃ l, g.arrange l ∧ l₁ = (l.drop skip).take j := by
  obtain ⟨l₀, rfl⟩ := exists_ofList g
  simp only [card_ofList] at fits
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, h₁⟩
    have pl := ofList_eq_iff.mp hl
    have p₁ := ofList_eq_iff.mp h₁
    have hlen : l.length = l₀.length := pl.length_eq
    have h1len : l₁.length = j := by rw [p₁.length_eq, List.length_take]; omega
    have hA : ((l.drop j).take skip).length = skip := by simp; omega
    refine ⟨(l.drop j).take skip ++ l₁ ++ (l.drop j).drop skip, ofList_eq_iff.mpr ?_, ?_⟩
    · calc List.Perm ((l.drop j).take skip ++ l₁ ++ (l.drop j).drop skip)
            (l₁ ++ (l.drop j).take skip ++ (l.drop j).drop skip) :=
            List.perm_append_comm.append_right _
          _ = l₁ ++ l.drop j := by rw [List.append_assoc, List.take_append_drop]
          List.Perm _ (l.take j ++ l.drop j) := p₁.append_right _
          _ = l := List.take_append_drop j l
          List.Perm _ l₀ := pl
    · rw [List.append_assoc, List.drop_left' hA, List.take_left' h1len]
  · rintro ⟨l, hl, rfl⟩
    have hlen : l.length = l₀.length := (ofList_eq_iff.mp hl).length_eq
    have hM : ((l.drop skip).take j).length = j := by simp; omega
    refine ⟨ofList ((l.drop skip).take j), (take_apply ..).mpr ⟨(l.drop skip).take j ++
      (l.take skip ++ (l.drop skip).drop j), ofList_eq_iff.mpr ?_, ?_⟩, rfl⟩
    · calc List.Perm ((l.drop skip).take j ++ (l.take skip ++ (l.drop skip).drop j))
            (l.take skip ++ ((l.drop skip).take j ++ (l.drop skip).drop j)) :=
            List.perm_append_comm_assoc _ _ _
          _ = l := by rw [List.take_append_drop, List.take_append_drop]
          List.Perm _ l₀ := ofList_eq_iff.mp hl
    · rw [List.take_left' hM]
#print axioms take_bind_arrange

end Bag

end BagResults
