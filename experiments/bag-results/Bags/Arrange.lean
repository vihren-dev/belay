import Bags.Algebra

/-!
# Arrangements of a bag

SQLite produces the rows of a bag in some order that it does not promise. `Bag.arrange b`
is the set of these orders. It is the one source of nondeterminism in this model: LIMIT
without ORDER BY, DISTINCT under a collation and order-sensitive aggregates are list
functions applied to an arrangement.
-/

namespace BagResults

namespace Bag
variable {α β : Type}

/-- The lists in which SQLite may produce the bag: the one source of nondeterminism. -/
def arrange (b : Bag α) : ND (List α) := fun l => ofList l = b

/-- For each bag `b` and list `l`: `l` is an arrangement of `b` if and only if the bag of `l`
is `b`. -/
@[simp] theorem arrange_apply (b : Bag α) (l : List α) : b.arrange l ↔ ofList l = b := Iff.rfl

/-- For each bag `b`: there is at least one arrangement of `b`. -/
theorem arrange_nonempty (b : Bag α) : ∃ l, b.arrange l :=
  Quotient.exists_rep b
#print axioms arrange_nonempty

/-- For all lists `l` and `m`: `m` is an arrangement of the bag of `l` if and only if `m` is
a permutation of `l`. -/
theorem arrange_ofList_iff {l m : List α} : (ofList l).arrange m ↔ m.Perm l :=
  ofList_eq_iff

/-- For each list function `f` that gives equal results on permutations, and each bag `b`:
`f` applied to an arbitrary arrangement of `b` is deterministic. Its one result is the value
of `f` on any list of `b`. Examples are count, min, max and the total of integers. -/
theorem map_arrange_of_perm (f : List α → β) (h : ∀ l m, l.Perm m → f l = f m) (b : Bag α) :
    f <$> b.arrange = pure (Quotient.lift f h b) := by
  induction b using induction_on with
  | of_list l =>
    refine ND.ext fun v => ⟨?_, fun eq => ⟨l, rfl, eq⟩⟩
    rintro ⟨m, eq, rfl⟩
    exact h _ _ (ofList_eq_iff.mp eq)
#print axioms map_arrange_of_perm

/-- For each function `f` and all lists `l` and `L`: if `L` is a permutation of `l.map f`,
then `L` is the map of a permutation of `l`. -/
theorem exists_perm_of_perm_map (f : α → β) {l : List α} {L : List β}
    (p : (l.map f).Perm L) : ∃ l' : List α, l'.Perm l ∧ l'.map f = L := by
  suffices ∀ {L₁ L₂ : List β}, L₁.Perm L₂ →
      ∀ l : List α, l.map f = L₁ → ∃ l' : List α, l'.Perm l ∧ l'.map f = L₂
    from this p l rfl
  intro L₁ L₂ p
  induction p with
  | nil => intro l e; exact ⟨l, .refl _, e⟩
  | cons x _ ih =>
    intro l e
    obtain ⟨y, l₀, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp e
    obtain ⟨l₀', p₀, e₀⟩ := ih l₀ rfl
    exact ⟨y :: l₀', p₀.cons y, by simp [e₀]⟩
  | swap x y _ =>
    intro l e
    obtain ⟨b, l₁, rfl, rfl, e₁⟩ := List.map_eq_cons_iff.mp e
    obtain ⟨a, l₀, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp e₁
    exact ⟨a :: b :: l₀, .swap b a l₀, rfl⟩
  | trans _ _ ih₁ ih₂ =>
    intro l e
    obtain ⟨l₁, p₁, e₁⟩ := ih₁ l e
    obtain ⟨l₂, p₂, e₂⟩ := ih₂ l₁ e₁
    exact ⟨l₂, p₂.trans p₁, e₂⟩
#print axioms exists_perm_of_perm_map

/-- For each function `f` and bag `b`: the arrangements of the mapped bag are the maps of the
arrangements of `b`. A projection commutes with the choice of an order. -/
theorem arrange_map (f : α → β) (b : Bag α) : (b.map f).arrange = List.map f <$> b.arrange := by
  induction b using induction_on with
  | of_list l =>
    refine ND.ext fun L => ⟨fun eq => ?_, ?_⟩
    · obtain ⟨l', p, rfl⟩ := exists_perm_of_perm_map f (ofList_eq_iff.mp eq).symm
      exact ⟨l', ofList_eq_iff.mpr p, rfl⟩
    · rintro ⟨l', eq, rfl⟩
      exact ofList_eq_iff.mpr ((ofList_eq_iff.mp eq).map f)
#print axioms arrange_map

/-- For each bag `b` and list `l` of `b`: every member of `l` is a member of `b`. -/
theorem mem_of_arrange {b : Bag α} {l : List α} (h : b.arrange l) {a : α} (m : a ∈ l) :
    a ∈ b := by
  rw [← (arrange_apply b l).mp h]
  exact m

end Bag

end BagResults
