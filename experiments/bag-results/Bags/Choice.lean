import Bags.Arrange

/-!
# LIMIT without ORDER BY

`Bag.take n b` keeps `n` rows of `b`. SQLite chooses which ones: the rows are the first `n`
of an arrangement. The rows are not determined, but their number is. A sub-bag of the right
size is exactly a possible result (`take_iff`).
-/

namespace BagResults

namespace Bag
variable {α : Type}

/-- LIMIT without ORDER BY: as many rows as the limit allows. SQLite chooses which ones. -/
def take (n : Nat) (b : Bag α) : ND (Bag α) := (fun l => ofList (l.take n)) <$> b.arrange

/-- For each limit `n` and all bags `b` and `c`: LIMIT `n` on `b` permits `c` if and only if
`c` is the bag of the first `n` rows of an arrangement of `b`. -/
theorem take_apply (n : Nat) (b c : Bag α) :
    b.take n c ↔ ∃ l, b.arrange l ∧ c = ofList (l.take n) := Iff.rfl

/-- A sub-bag: `c` is a sub-bag of `b` when `b` is the union of `c` and some bag `d`. -/
def Sub (c b : Bag α) : Prop := ∃ d, b = c ++ d

/-- For each bag `b`: `b` is a sub-bag of itself. -/
theorem Sub.refl (b : Bag α) : b.Sub b := ⟨ofList [], (append_nil b).symm⟩

/-- For all bags `e`, `c` and `b`: if `e` is a sub-bag of `c` and `c` is a sub-bag of `b`,
then `e` is a sub-bag of `b`. -/
theorem Sub.trans {e c b : Bag α} (ec : e.Sub c) (cb : c.Sub b) : e.Sub b := by
  obtain ⟨d, rfl⟩ := ec
  obtain ⟨d', rfl⟩ := cb
  exact ⟨d ++ d', append_assoc e d d'⟩

/-- For each limit `n` and all bags `b` and `c`: `c` is a possible result of LIMIT `n` on `b`
if and only if `c` is a sub-bag of `b` with `min n (card b)` rows. -/
theorem take_iff (n : Nat) (b c : Bag α) : b.take n c ↔ c.Sub b ∧ c.card = min n b.card := by
  constructor
  · rintro ⟨l, eq, rfl⟩
    subst eq
    refine ⟨⟨ofList (l.drop n), ?_⟩, ?_⟩
    · rw [ofList_append, List.take_append_drop]
    · simp [List.length_take]
  · rintro ⟨⟨d, rfl⟩, hc⟩
    obtain ⟨lc, rfl⟩ := exists_ofList c
    obtain ⟨ld, rfl⟩ := exists_ofList d
    refine (take_apply ..).mpr ⟨lc ++ ld, rfl, ?_⟩
    simp only [ofList_append, card_ofList, List.length_append] at hc ⊢
    congr 1
    rw [List.take_append, List.take_of_length_le (by omega)]
    rcases (by omega : n ≤ lc.length ∨ ld.length = 0) with short | empty
    · rw [Nat.sub_eq_zero_of_le short, List.take_zero, List.append_nil]
    · rw [List.length_eq_zero_iff.mp empty, List.take_nil, List.append_nil]
#print axioms take_iff

/-- For each limit `n` and bag `b`: every possible result of LIMIT `n` on `b` has
`min n (card b)` rows. The rows are not determined, their number is. -/
theorem card_take (n : Nat) (b : Bag α) : card <$> b.take n = pure (min n b.card) := by
  refine ND.ext fun v => ⟨?_, ?_⟩
  · rintro ⟨c, hc, rfl⟩
    exact ((take_iff n b c).mp hc).2
  · rintro rfl
    obtain ⟨l, rfl⟩ := exists_ofList b
    refine ⟨_, (take_apply ..).mpr ⟨l, rfl, rfl⟩, ?_⟩
    show min n l.length = (l.take n).length
    simp
#print axioms card_take

/-- For each limit `n` and bag `b` with at most `n` rows: LIMIT `n` keeps all rows of `b`,
and the result is deterministic. -/
theorem take_of_card_le {n : Nat} {b : Bag α} (h : b.card ≤ n) : b.take n = pure b := by
  refine ND.ext fun c => ?_
  rw [take_apply, ND.pure_apply]
  constructor
  · rintro ⟨l, eq, rfl⟩
    subst eq
    rw [List.take_of_length_le h]
  · rintro rfl
    obtain ⟨l, rfl⟩ := exists_ofList c
    exact ⟨l, rfl, by rw [List.take_of_length_le h]⟩
#print axioms take_of_card_le

/-- For all limits `m` and `n` and each bag `b`: LIMIT `n` on a result of LIMIT `m` permits
the same bags as one LIMIT `min n m`. -/
theorem take_take (m n : Nat) (b : Bag α) :
    (b.take m >>= Bag.take n) = b.take (min n m) := by
  refine ND.ext fun e => ?_
  simp only [ND.bind_apply, take_iff]
  constructor
  · rintro ⟨c, ⟨hcb, hc⟩, hec, he⟩
    exact ⟨hec.trans hcb, by rw [he, hc]; omega⟩
  · rintro ⟨⟨d, rfl⟩, he⟩
    obtain ⟨ld, rfl⟩ := exists_ofList d
    simp only [card_append, card_ofList] at he ⊢
    refine ⟨e ++ ofList (ld.take (min m (e.card + ld.length) - e.card)),
      ⟨⟨ofList (ld.drop (min m (e.card + ld.length) - e.card)), ?_⟩, ?_⟩,
      ⟨ofList (ld.take (min m (e.card + ld.length) - e.card)), rfl⟩, ?_⟩
    · rw [append_assoc, ofList_append, List.take_append_drop]
    · simp only [card_append, card_ofList, List.length_take]
      omega
    · simp only [card_append, card_ofList, List.length_take]
      omega
#print axioms take_take

/-- There is a bag `b` of numbers and a condition `p` such that a filter by `p` after LIMIT 1
permits other bags than LIMIT 1 after the filter. WHERE and LIMIT do not commute. -/
theorem filter_take_not_comm :
    ∃ (b : Bag Nat) (p : Nat → Bool), (Bag.filter p <$> b.take 1) ≠ (b.filter p).take 1 := by
  refine ⟨ofList [1, 2], (· == 1), fun same => ?_⟩
  have left : (Bag.filter (· == 1) <$> (ofList [1, 2]).take 1) (ofList []) :=
    ⟨ofList [2], (take_apply ..).mpr ⟨[2, 1], ofList_eq_iff.mpr (.swap 1 2 []), rfl⟩, rfl⟩
  rw [same, take_iff] at left
  exact absurd left.2 (by decide)
#print axioms filter_take_not_comm

/-- An aggregate that reads its rows in an order SQLite does not promise, as group_concat
without ORDER BY does. -/
def aggregate {β : Type} (f : List α → β) (b : Bag α) : ND β := f <$> b.arrange

/-- For each list function `f` that gives equal results on permutations, and each bag `b`:
the aggregate `f` of `b` is deterministic. -/
theorem aggregate_of_perm {β : Type} (f : List α → β) (h : ∀ l m, l.Perm m → f l = f m)
    (b : Bag α) : b.aggregate f = pure (Quotient.lift f h b) :=
  map_arrange_of_perm f h b
#print axioms aggregate_of_perm

end Bag

end BagResults
