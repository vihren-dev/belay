import Bags.CanonicalUnique
import Bags.Rank

/-!
# Observational equivalence of queries

An application reads one list of rows per run. Two queries are equivalent when they permit
the same lists. For results without ORDER BY this is equality of the sets of permitted bags.
For one deterministic ranking it is equality of canonical forms. For sets of rankings it is
weaker than equality of the sets of canonical forms.
-/

namespace BagResults
variable {α : Type}

/-- The lists that the application may read from a query's result. -/
def observe (m : ND (Ranked α)) : ND (List α) := m >>= Ranked.arrange

/-- Two queries are equivalent when they permit the same lists. -/
def Equivalent (m₁ m₂ : ND (Ranked α)) : Prop := observe m₁ = observe m₂

/-- Each query is equivalent to itself, equivalence is symmetric, and it is transitive. -/
theorem equivalent_equivalence : Equivalence (@Equivalent α) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
#print axioms equivalent_equivalence

/-- For each ranking `r`: the deterministic result `r` permits the lists that `r` permits. -/
@[simp] theorem observe_pure (r : Ranked α) : observe (pure r) = r.arrange :=
  ND.ext fun _ => ⟨fun ⟨_, e, h⟩ => e ▸ h, fun h => ⟨r, rfl, h⟩⟩

/-- For all sets of bags `m₁` and `m₂`, read as results without ORDER BY: the results are
equivalent if and only if `m₁ = m₂`. -/
theorem equivalent_unordered (m₁ m₂ : ND (Bag α)) :
    Equivalent (Ranked.ofBag <$> m₁) (Ranked.ofBag <$> m₂) ↔ m₁ = m₂ := by
  have reads (m : ND (Bag α)) (l : List α) :
      observe (Ranked.ofBag <$> m) l ↔ m (Bag.ofList l) := by
    simp only [observe, ND.bind_apply, ND.map_apply, Ranked.ofBag]
    constructor
    · rintro ⟨_, ⟨b, mb, rfl⟩, l', eq, _, rfl, rfl⟩
      rw [List.append_nil, eq]
      exact mb
    · intro mb
      exact ⟨_, ⟨_, mb, rfl⟩, l, rfl, [], rfl, by simp⟩
  constructor
  · intro same
    funext b
    apply propext
    obtain ⟨l, rfl⟩ := Bag.arrange_nonempty b
    show m₁ (Bag.ofList l) ↔ m₂ (Bag.ofList l)
    rw [← reads m₁ l, ← reads m₂ l, congrArg (· l) same]
  · rintro rfl
    rfl
#print axioms equivalent_unordered

/-- For all rankings `r` and `r'` of a type with decidable equality: the deterministic
results `r` and `r'` are equivalent if and only if their canonical forms are equal. -/
theorem equivalent_pure_iff [DecidableEq α] (r r' : Ranked α) :
    Equivalent (pure r) (pure r') ↔ r.canon = r'.canon := by
  rw [Equivalent, observe_pure, observe_pure]
  exact Ranked.arrange_eq_iff_canon r r'
#print axioms equivalent_pure_iff

/-- For all different rows `a` and `b`: the result with the one ranking `[{a, b}]` and the
result with the two rankings `[{a}, {b}]` and `[{b}, {a}]` are equivalent, but the sets of
their canonical forms differ. Equivalence of results with several rankings is not equality
of their sets of canonical forms.
Proof sketch: both results permit exactly the lists `[a, b]` and `[b, a]`: the one group
permits the two orders of its rows, and each ranking of two groups of one row permits one
list. The canonical form keeps the group `{a, b}`, because its rows differ, and keeps the two
rankings of one row each, so `[{a}, {b}]` is a canonical form of the second result but not of
the first. -/
theorem equivalent_but_canonical_results_differ [DecidableEq α] {a b : α} (ab : a ≠ b) :
    let one : ND (Ranked α) := pure [Bag.ofList [a, b]]
    let two : ND (Ranked α) := fun r =>
      r = [Bag.ofList [a], Bag.ofList [b]] ∨ r = [Bag.ofList [b], Bag.ofList [a]]
    Equivalent one two ∧ (Ranked.canon <$> one) ≠ (Ranked.canon <$> two) := by
  intro one two
  have singles (x y : α) : Ranked.arrange [Bag.ofList [x], Bag.ofList [y]] = pure [x, y] :=
    Ranked.arrange_singletons [x, y]
  refine ⟨ND.ext fun L => ?_, fun same => ?_⟩
  · rw [observe_pure, Ranked.arrange_singleton, Bag.arrange_ofList_iff]
    constructor
    · intro p
      obtain ⟨x, y, rfl⟩ : ∃ x y, L = [x, y] := by
        match L, p.length_eq with
        | [x, y], _ => exact ⟨x, y, rfl⟩
      by_cases hx : x = a
      · rw [hx] at p ⊢
        have hy : y = b := (List.perm_cons a).mp p |> List.perm_singleton.mp |> List.cons.inj |>.1
        refine ⟨_, Or.inl rfl, ?_⟩
        rw [singles, hy]
        rfl
      · have hxb : x = b := by simpa [hx] using p.mem_iff.mp (List.mem_cons_self ..)
        rw [hxb] at p ⊢
        have hy : y = a := (List.perm_cons b).mp (p.trans (.swap b a [])) |>
          List.perm_singleton.mp |> List.cons.inj |>.1
        refine ⟨_, Or.inr rfl, ?_⟩
        rw [singles, hy]
        rfl
    · rintro ⟨r, hr | hr, hL⟩ <;> subst hr <;> rw [singles] at hL <;>
        rw [(ND.pure_apply _ _).mp hL]
      exact .swap a b []
  · have fixed : [Bag.ofList [a], Bag.ofList [b]] =
        Ranked.canon [Bag.ofList [a], Bag.ofList [b]] := by
      simp [Ranked.canon, Ranked.canonGroupOfList, Ranked.allEqual]
    have h := (congrFun same [Bag.ofList [a], Bag.ofList [b]]).mpr ⟨_, Or.inl rfl, fixed⟩
    obtain ⟨r, rfl, e⟩ := h
    have := congrArg (List.map Bag.card) e
    simp [Ranked.canon, Ranked.canonGroupOfList, Ranked.allEqual, ab] at this
#print axioms equivalent_but_canonical_results_differ

end BagResults
