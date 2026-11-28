import Bags.Canonical

/-!
# The canonical form is unique

The set of lists that a ranking in canonical form permits determines the ranking. The first
group is the bag of the first `n` rows of any permitted list, where `n` is the size of the
group: a smaller `n` does not determine the bag, because a group with more than one row has
two different rows.
-/

namespace BagResults

namespace Ranked
variable {α : Type}

/-- For each group `g` in canonical form: `g` has at least one row. -/
theorem GroupCanonical.card_pos {g : Bag α} (h : GroupCanonical g) : 0 < g.card := by
  rcases h with h | ⟨a, ha, _⟩
  · omega
  · obtain ⟨l, rfl⟩ := g.exists_ofList
    exact List.length_pos_of_mem ha

/-- For each group `g`, groups `gs` and list `L` that `g :: gs` permits: the first `card g`
rows of `L` are the rows of `g`. -/
theorem first_group_fixed {g : Bag α} {gs : Ranked α} {L : List α} (h : arrange (g :: gs) L) :
    Bag.ofList (L.take g.card) = g := by
  obtain ⟨l₁, h₁, l₂, _, rfl⟩ := h
  rw [List.take_left' (by rw [← h₁]; rfl)]
  exact h₁

/-- For each group `g` with two different rows, groups `gs` and number `k` with
`0 < k < card g`: there are two lists that `g :: gs` permits whose first `k` rows form
different bags. -/
theorem first_group_varies {g : Bag α} (gs : Ranked α) (two : ∃ a ∈ g, ∃ b ∈ g, a ≠ b)
    {k : Nat} (pos : 0 < k) (lt : k < g.card) :
    ∃ L₁ L₂, arrange (g :: gs) L₁ ∧ arrange (g :: gs) L₂ ∧
      Bag.ofList (L₁.take k) ≠ Bag.ofList (L₂.take k) := by
  classical
  obtain ⟨l, rfl⟩ := g.exists_ofList
  obtain ⟨a, ha, b, hb, ab⟩ := two
  have hb' : b ∈ l.erase a := (List.mem_erase_of_ne (Ne.symm ab)).mpr hb
  have pl : l.Perm (a :: b :: (l.erase a).erase b) :=
    (List.perm_cons_erase ha).trans ((List.perm_cons_erase hb').cons a)
  generalize (l.erase a).erase b = d at pl
  obtain ⟨m, hm⟩ := arrange_nonempty gs
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk : k' ≤ d.length := by
    have := pl.length_eq
    simp only [Bag.card_ofList] at lt
    simp only [List.length_cons] at this
    omega
  have start (x y : α) : (x :: (d ++ [y]) ++ m).take (k' + 1) = [x] ++ d.take k' := by
    rw [List.cons_append, List.take_succ_cons, List.append_assoc,
      List.take_append_of_le_length hk]
    rfl
  refine ⟨a :: (d ++ [b]) ++ m, b :: (d ++ [a]) ++ m, ⟨a :: (d ++ [b]), ?_, m, hm, rfl⟩,
    ⟨b :: (d ++ [a]), ?_, m, hm, rfl⟩, ?_⟩
  · exact Bag.ofList_eq_iff.mpr (((List.perm_append_singleton b d).cons a).trans pl.symm)
  · exact Bag.ofList_eq_iff.mpr
      ((((List.perm_append_singleton a d).cons b).trans (.swap a b d)).trans pl.symm)
  · intro eq
    rw [start a b, start b a, Bag.ofList_eq_iff, List.perm_append_right_iff,
      List.singleton_perm_singleton] at eq
    exact ab eq

/-- For all rankings `c` and `c'` whose groups are in canonical form: if `c` and `c'` permit
the same lists, then `c = c'`.
Proof sketch: induction on `c`. A ranking with a group permits a nonempty list, so both are
empty or both are not. The first groups have the same size: else the smaller size `k` fixes
the bag of the first `k` rows for one ranking but not for the other. Then the first groups
are the bag of the first rows of a common list, and the other groups permit the same
lists. -/
theorem eq_of_arrange_eq_of_canonical : ∀ (c c' : Ranked α), (∀ g ∈ c, GroupCanonical g) →
    (∀ g ∈ c', GroupCanonical g) → c.arrange = c'.arrange → c = c'
  | [], [], _, _, _ => rfl
  | [], g' :: gs', _, hc', same => by
    obtain ⟨L, hL⟩ := arrange_nonempty (g' :: gs')
    have empty : L = [] := (congrFun same L).mpr hL
    have pos := (hc' g' (List.mem_cons_self ..)).card_pos
    rw [← first_group_fixed hL, empty] at pos
    simp at pos
  | g :: gs, [], hc, _, same => by
    obtain ⟨L, hL⟩ := arrange_nonempty (g :: gs)
    have empty : L = [] := (congrFun same L).mp hL
    have pos := (hc g (List.mem_cons_self ..)).card_pos
    rw [← first_group_fixed hL, empty] at pos
    simp at pos
  | g :: gs, g' :: gs', hc, hc', same => by
    have not_less : ∀ (g g' : Bag α) (gs gs' : Ranked α), GroupCanonical g →
        GroupCanonical g' → arrange (g :: gs) = arrange (g' :: gs') → ¬ g.card < g'.card := by
      intro g g' gs gs' cg cg' same lt
      have two : ∃ a ∈ g', ∃ b ∈ g', a ≠ b := cg'.resolve_left (by have := cg.card_pos; omega)
      obtain ⟨L₁, L₂, h₁, h₂, ne⟩ := first_group_varies gs' two cg.card_pos lt
      rw [← same] at h₁ h₂
      exact ne ((first_group_fixed h₁).trans (first_group_fixed h₂).symm)
    have cg := hc g (List.mem_cons_self ..)
    have cg' := hc' g' (List.mem_cons_self ..)
    have size : g.card = g'.card := Nat.le_antisymm
      (Nat.not_lt.mp (not_less g' g gs' gs cg' cg same.symm))
      (Nat.not_lt.mp (not_less g g' gs gs' cg cg' same))
    obtain ⟨L, hL⟩ := arrange_nonempty (g :: gs)
    have hL' : arrange (g' :: gs') L := (congrFun same L).mp hL
    have first : g = g' := calc
      g = Bag.ofList (L.take g.card) := (first_group_fixed hL).symm
      _ = Bag.ofList (L.take g'.card) := by rw [size]
      _ = g' := first_group_fixed hL'
    subst first
    have move (r r' : Ranked α) (same : arrange (g :: r) = arrange (g :: r')) (m : List α)
        (hm : arrange r m) : arrange r' m := by
      obtain ⟨l, hl⟩ := g.arrange_nonempty
      obtain ⟨l', hl', m', hm', e⟩ := (congrFun same (l ++ m)).mp ⟨l, hl, m, hm, rfl⟩
      have len : l.length = l'.length := by rw [← hl] at hl'; exact (Bag.ofList_eq_iff.mp hl').symm.length_eq
      rw [List.append_inj_right e len]
      exact hm'
    have tails : arrange gs = arrange gs' :=
      ND.ext fun m => ⟨move gs gs' same m, move gs' gs same.symm m⟩
    rw [eq_of_arrange_eq_of_canonical gs gs'
      (fun h hh => hc h (List.mem_cons_of_mem _ hh))
      (fun h hh => hc' h (List.mem_cons_of_mem _ hh)) tails]
#print axioms eq_of_arrange_eq_of_canonical

/-- For all rankings `r` and `r'` of a type with decidable equality: `r` and `r'` permit the
same lists if and only if their canonical forms are equal. -/
theorem arrange_eq_iff_canon [DecidableEq α] (r r' : Ranked α) :
    r.arrange = r'.arrange ↔ r.canon = r'.canon :=
  ⟨fun h => eq_of_arrange_eq_of_canonical _ _ (canon_canonical r) (canon_canonical r')
      (by rw [arrange_canon, arrange_canon, h]),
    fun h => by rw [← arrange_canon r, h, arrange_canon]⟩
#print axioms arrange_eq_iff_canon

/-- For each row `a` and number `n`: `n` groups that each hold the one row `a` permit the
same lists as one group with `n` copies of `a`. A comparison of rankings by their data needs
the canonical form. -/
theorem arrange_replicate_singletons (a : α) (n : Nat) :
    arrange (List.replicate n (Bag.ofList [a])) = arrange [Bag.ofList (List.replicate n a)] := by
  classical
  refine (arrange_eq_iff_canon _ _).mpr ?_
  have one : canonGroup (Bag.ofList [a]) = [Bag.ofList [a]] := by
    simp [canonGroupOfList, allEqual]
  have all : allEqual (List.replicate n a) = true :=
    (allEqual_iff _).mpr fun x hx y hy => (List.eq_of_mem_replicate hx).trans
      (List.eq_of_mem_replicate hy).symm
  have singles : ∀ n, List.flatMap canonGroup (List.replicate n (Bag.ofList [a])) =
      List.replicate n (Bag.ofList [a]) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.flatMap_cons, one, ih]; rfl
  simp only [canon, List.flatMap_cons, List.flatMap_nil, List.append_nil, canonGroup_ofList,
    canonGroupOfList, all, ite_true, List.map_replicate, singles]
#print axioms arrange_replicate_singletons

/-- For each row `a`: two groups `{a}` and `{a}` permit the same lists as one group
`{a, a}`. -/
theorem arrange_equal_rows (a : α) :
    arrange [Bag.ofList [a], Bag.ofList [a]] = arrange [Bag.ofList [a, a]] :=
  arrange_replicate_singletons a 2
#print axioms arrange_equal_rows

end Ranked

end BagResults
