import Bags.TieGroups

/-!
# ORDER BY

`rank le b` sorts an arrangement of `b` with a stable merge sort and splits the result into
tie groups. For a total preorder the result does not depend on the arrangement
(`rank_deterministic`). Without ORDER BY every pair of rows ties, and the rows form one
group (`observe_rank_trivial`).
-/

namespace BagResults

namespace Ranked
variable {α : Type} (le : α → α → Bool)

/-- For each total and transitive `le` and all lists `s` and `t` sorted by `le`: if `t` is a
permutation of `s`, then the tie groups of `s` and `t` are equal as bags.
Proof sketch: induction on a bound of the length. The first rows `x` of `s` and `y` of `t`
tie, so the same rows tie `x` and `y`. The first groups are the rows that tie `x`, a
permutation in `s` and `t`. The other groups are the tie groups of the sorted rows that do
not tie `x`, which are shorter permutations. -/
theorem tieGroups_bags_eq_of_perm (total : ∀ x y, (le x y || le y x) = true)
    (trans : ∀ x y z, le x y = true → le y z = true → le x z = true) :
    ∀ (n : Nat) (s t : List α), s.length ≤ n → s.Pairwise (fun u v => le u v = true) →
      t.Pairwise (fun u v => le u v = true) → s.Perm t →
      (tieGroups (ties le) s).map Bag.ofList = (tieGroups (ties le) t).map Bag.ofList := by
  have refl : ∀ u, le u u = true := fun u => by simpa using total u u
  have ties_iff : ∀ u v, ties le u v = true ↔ le u v = true ∧ le v u = true := by
    simp [ties]
  intro n
  induction n with
  | zero =>
    intro s t hs _ _ p
    obtain rfl := List.length_eq_zero_iff.mp (Nat.le_zero.mp hs)
    rw [← p.nil_eq]
  | succ n ih =>
    intro s t hs ss st p
    match s, t, p with
    | [], _, p => rw [← p.nil_eq]
    | _ :: _, [], p => exact absurd p.eq_nil (List.cons_ne_nil _ _)
    | x :: xs, y :: ys, p =>
      have below (z : α) (w : α) (zs : List α) (sorted : (z :: zs).Pairwise
          (fun u v => le u v = true)) (hw : w ∈ z :: zs) : le z w = true := by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact refl w
        · exact (List.pairwise_cons.mp sorted).1 w hw
      have hxy : ties le x y = true := (ties_iff x y).mpr
        ⟨below x y xs ss (p.mem_iff.mpr (by simp)), below y x ys st (p.mem_iff.mp (by simp))⟩
      have same : ties le y = ties le x := funext fun z => by
        apply Bool.eq_iff_iff.mpr
        have h := (ties_iff x y).mp hxy
        simp only [ties_iff]
        exact ⟨fun ⟨a, b⟩ => ⟨trans x y z h.1 a, trans z y x b h.2⟩,
          fun ⟨a, b⟩ => ⟨trans y x z h.2 a, trans z x y b h.1⟩⟩
      rw [tieGroups_sorted_cons le total trans x xs ss,
        tieGroups_sorted_cons le total trans y ys st, same]
      simp only [List.map_cons]
      congr 1
      · exact Bag.ofList_eq_iff.mpr (p.filter _)
      · refine ih _ _ ?_ (ss.filter _) (st.filter _) (p.filter _)
        have : ties le x x = true := (ties_iff x x).mpr ⟨refl x, refl x⟩
        simp only [List.filter_cons, this, Bool.not_true]
        simp only [List.length_cons] at hs
        exact Nat.le_trans (List.length_filter_le _ _) (by simpa using hs)
#print axioms tieGroups_bags_eq_of_perm

/-- ORDER BY with a total preorder `le`: a stable sort of an arrangement, split into tie
groups. Without ORDER BY, every pair of rows ties and the bag is one group. -/
def rank (b : Bag α) : ND (Ranked α) :=
  (fun l => (tieGroups (ties le) (l.mergeSort le)).map Bag.ofList) <$> b.arrange

/-- For each total and transitive `le` and each bag `b`: there is one ranking `r` such that
`rank le b` permits only `r`. The ranking does not depend on the arrangement. -/
theorem rank_deterministic (total : ∀ x y, le x y || le y x)
    (trans : ∀ x y z, le x y → le y z → le x z) (b : Bag α) : ∃ r, rank le b = pure r :=
  ⟨_, Bag.map_arrange_of_perm _ (fun l m p =>
    tieGroups_bags_eq_of_perm le total trans _ (l.mergeSort le) (m.mergeSort le) (Nat.le_refl _)
      (List.pairwise_mergeSort trans total l) (List.pairwise_mergeSort trans total m)
      ((List.mergeSort_perm l le).trans (p.trans (List.mergeSort_perm m le).symm))) b⟩
#print axioms rank_deterministic

/-- For every list of lists `gs`: the union of the bags of the lists in `gs` is the bag of
the concatenation of `gs`. -/
private theorem toBag_ofLists (gs : List (List α)) :
    toBag (gs.map Bag.ofList) = Bag.ofList gs.flatten := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, toBag, List.foldr_cons] at ih ⊢; rw [ih]; rfl

/-- For each `le` and bag `b`: `rank le b` gives at least one ranking, and the rows of each
ranking that it gives are exactly the rows of `b`, with their duplicates. So a reader whose
result is a function of the bag of rows gives the same result with and without ORDER BY. This
says nothing about readers that see the order: a scalar subquery reads its first row (probe
P11), and an outer `group_concat` can read the order of a FROM subquery (probe P12). The
theorem does not model errors: in SQLite a sort key can fail, and `le` here is a total
function. -/
theorem toBag_rank (b : Bag α) : toBag <$> rank le b = pure b := by
  induction b using Bag.induction_on with
  | of_list l =>
    have same (m : List α) (eq : Bag.ofList m = Bag.ofList l) :
        toBag ((tieGroups (ties le) (m.mergeSort le)).map Bag.ofList) = Bag.ofList l := by
      rw [toBag_ofLists, flatten_tieGroups, ← eq]
      exact Quotient.sound (List.mergeSort_perm m le)
    refine ND.ext fun v => ⟨?_, ?_⟩
    · rintro ⟨r, ⟨m, eq, rfl⟩, rfl⟩
      exact same m eq
    · rintro rfl
      exact ⟨_, ⟨l, rfl, rfl⟩, (same l rfl).symm⟩
#print axioms toBag_rank

/-- For each `le` and bag `b`: if `le x y` holds for all rows `x` and `y` of `b`, then the
lists that the ranking permits are the arrangements of `b`. Every pair of rows ties, so the
ranking of a bag with rows is one group; the ranking of the empty bag has no group and permits
only the empty list. -/
theorem rank_arrange_of_all_tie (b : Bag α) (all_tie : ∀ x ∈ b, ∀ y ∈ b, le x y = true) :
    (rank le b >>= arrange) = b.arrange := by
  have key (m : List α) (hm : b.arrange m) :
      arrange ((tieGroups (ties le) (m.mergeSort le)).map Bag.ofList) = b.arrange := by
    have inside := fun x (hx : x ∈ m) => Bag.mem_of_arrange hm hx
    rw [List.mergeSort_of_pairwise (List.pairwise_of_forall_mem_list fun x hx y hy =>
      all_tie x (inside x hx) y (inside y hy))]
    rw [← (Bag.arrange_apply b m).mp hm]
    cases m with
    | nil => exact ND.ext fun l => by simp [tieGroups, Bag.ofList_eq_iff]
    | cons x xs =>
      have h := tieGroups_append (ties le) [] (x :: xs) (by simp)
        (fun u hu v hv => by simp [ties, all_tie u (inside u hu) v (inside v hv),
          all_tie v (inside v hv) u (inside u hu)]) (by simp)
      rw [List.append_nil] at h
      rw [h]
      exact arrange_singleton _
  refine ND.ext fun L => ⟨?_, fun hL => ⟨_, ⟨L, hL, rfl⟩, by rw [key L hL]; exact hL⟩⟩
  rintro ⟨r, ⟨m, hm, rfl⟩, hr⟩
  rwa [key m hm] at hr
#print axioms rank_arrange_of_all_tie

/-- For each bag `b`: with `le := fun _ _ => true` the lists that the ranking permits are
exactly the arrangements of `b`. A query without ORDER BY is one tie group. -/
theorem observe_rank_trivial (b : Bag α) :
    (rank (fun _ _ => true) b >>= arrange) = b.arrange :=
  rank_arrange_of_all_tie _ b fun _ _ _ _ => rfl
#print axioms observe_rank_trivial

end Ranked

end BagResults
