import Bags.Ranked

/-!
# Tie groups of a sorted list

ORDER BY sorts the rows and then splits them into runs of rows that tie. This file shows that
for a total preorder the tie groups of a sorted list, as bags, depend only on the bag of the
list: two sorted permutations of each other have the same tie groups up to the order inside
each group.
-/

namespace BagResults

namespace Ranked
variable {α : Type}

/-- The longest runs of adjacent rows that tie. -/
def tieGroups (tie : α → α → Bool) : List α → List (List α)
  | [] => []
  | x :: xs => match tieGroups tie xs with
    | (y :: g) :: gs => if tie x y then (x :: y :: g) :: gs else [x] :: (y :: g) :: gs
    | [] :: gs => [x] :: gs
    | [] => [[x]]

/-- For each `tie` and list `l`: the tie groups of `l`, concatenated, are `l`. -/
theorem flatten_tieGroups (tie : α → α → Bool) (l : List α) : (tieGroups tie l).flatten = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    unfold tieGroups
    split <;> rename_i h <;> rw [h] at ih
    · split <;> simp_all
    · simp_all
    · simp_all

/-- For each `tie`, row `y` and list `rest`: the first tie group of `y :: rest` starts with
`y`. -/
theorem tieGroups_cons_shape (tie : α → α → Bool) (y : α) (rest : List α) :
    ∃ g gs, tieGroups tie (y :: rest) = (y :: g) :: gs := by
  unfold tieGroups
  split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨[], _, rfl⟩
  · exact ⟨[], _, rfl⟩
  · exact ⟨[], _, rfl⟩

/-- For each `tie` and all lists `g` and `rest`: if `g` is not empty, all rows of `g` tie,
and no row of `g` ties the first row of `rest`, then `g` is the first tie group of
`g ++ rest`, and the other groups are the tie groups of `rest`. -/
theorem tieGroups_append (tie : α → α → Bool) (rest : List α) :
    ∀ g : List α, g ≠ [] → (∀ u ∈ g, ∀ v ∈ g, tie u v = true) →
      (∀ u ∈ g, ∀ v ∈ rest.head?, tie u v = false) →
      tieGroups tie (g ++ rest) = g :: tieGroups tie rest
  | [], ne, _, _ => absurd rfl ne
  | [a], _, _, apart => by
    match rest, apart with
    | [], _ => rfl
    | y :: rest', apart =>
      obtain ⟨g', gs, e⟩ := tieGroups_cons_shape tie y rest'
      rw [List.singleton_append, tieGroups, e]
      simp [apart a (by simp) y (by simp)]
  | a :: b :: g, _, ties, apart => by
    have ih := tieGroups_append tie rest (b :: g) (by simp)
      (fun u hu v hv => ties u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv))
      (fun u hu v hv => apart u (List.mem_cons_of_mem _ hu) v hv)
    rw [List.cons_append, tieGroups, ih]
    simp [ties a (by simp) b (by simp)]
#print axioms tieGroups_append

/-- Two rows tie under `le` when each is at most the other. -/
def ties (le : α → α → Bool) (x y : α) : Bool := le x y && le y x

/-- For each condition `p` and list `l`: if along `l` a row that satisfies `p` never follows
a row that fails `p`, then `l` is the rows that satisfy `p` followed by the rows that fail
`p`. -/
theorem eq_filter_append_filter (p : α → Bool) :
    ∀ l : List α, l.Pairwise (fun u v => p v = true → p u = true) →
      l = l.filter p ++ l.filter (fun x => !p x)
  | [], _ => rfl
  | u :: l, h => by
    rw [List.pairwise_cons] at h
    cases hu : p u
    · have none : ∀ v ∈ l, p v = false := fun v hv => by
        cases hv' : p v
        · rfl
        · exact absurd (h.1 v hv hv') (by simp [hu])
      have kept : l.filter p = [] := List.filter_eq_nil_iff.mpr fun v hv => by simp [none v hv]
      have dropped : l.filter (fun x => !p x) = l :=
        List.filter_eq_self.mpr fun v hv => by simp [none v hv]
      simp [hu, kept, dropped]
    · have ih := eq_filter_append_filter p l h.2
      simp only [List.filter_cons, hu, Bool.not_true]
      simpa using ih

variable (le : α → α → Bool)

/-- For each total and transitive `le`, row `x` and list `xs` with `x :: xs` sorted by `le`:
the first tie group of `x :: xs` is the rows that tie `x`, and the other groups are the tie
groups of the rows that do not tie `x`.
Proof sketch: in a sorted list the rows that tie the first row form a prefix, because a row
between two rows that tie `x` also ties `x`. The rows of the prefix tie each other, and no
row of the prefix ties the first row after it, so `tieGroups_append` applies. -/
theorem tieGroups_sorted_cons (total : ∀ x y, (le x y || le y x) = true)
    (trans : ∀ x y z, le x y = true → le y z = true → le x z = true) (x : α) (xs : List α)
    (sorted : (x :: xs).Pairwise (fun u v => le u v = true)) :
    tieGroups (ties le) (x :: xs) = (x :: xs).filter (ties le x) ::
      tieGroups (ties le) ((x :: xs).filter (fun v => !ties le x v)) := by
  have refl : ∀ u, le u u = true := fun u => by simpa using total u u
  have first : ∀ u ∈ x :: xs, le x u = true := fun u hu => by
    rcases List.mem_cons.mp hu with rfl | hu
    · exact refl u
    · exact (List.pairwise_cons.mp sorted).1 u hu
  have ties_iff : ∀ u v, ties le u v = true ↔ le u v = true ∧ le v u = true := by
    simp [ties]
  have prefix_ties : (x :: xs).Pairwise (fun u v => ties le x v = true → ties le x u = true) :=
    sorted.imp_of_mem fun {u v} hu _ huv hxv => (ties_iff x u).mpr
      ⟨first u hu, trans u v x huv ((ties_iff x v).mp hxv).2⟩
  have split := eq_filter_append_filter (ties le x) (x :: xs) prefix_ties
  have h := tieGroups_append (ties le) ((x :: xs).filter fun v => !ties le x v)
    ((x :: xs).filter (ties le x)) (List.ne_nil_of_mem (a := x) (by simp [ties, refl]))
    (fun u hu v hv => by
      have hu := ((ties_iff x u).mp (List.mem_filter.mp hu).2)
      have hv := ((ties_iff x v).mp (List.mem_filter.mp hv).2)
      exact (ties_iff u v).mpr ⟨trans u x v hu.2 hv.1, trans v x u hv.2 hu.1⟩)
    (fun u hu v hv => by
      have hu := ((ties_iff x u).mp (List.mem_filter.mp hu).2)
      have hv := (List.mem_filter.mp (List.mem_of_mem_head? hv)).2
      cases huv : ties le u v
      · rfl
      · have huv := (ties_iff u v).mp huv
        have : ties le x v = true :=
          (ties_iff x v).mpr ⟨trans x u v hu.1 huv.1, trans v u x huv.2 hu.2⟩
        simp [this] at hv)
  rwa [← split] at h
#print axioms tieGroups_sorted_cons

end Ranked

end BagResults
