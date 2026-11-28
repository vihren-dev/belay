import Bags.Slice

/-!
# OFFSET and LIMIT over ranked rows

`Ranked.window skip keep r` applies OFFSET `skip` and LIMIT `keep` to ranked rows group by
group. Groups before the window are skipped, groups inside it are kept, and a group that the
window cuts keeps a sub-bag of the right size. The lists that the window permits are the
slices of the lists that `r` permits (`window_arrange`).
-/

namespace BagResults

namespace Ranked
variable {α : Type}

/-- OFFSET `skip` and LIMIT `keep` over ranked rows. A group with at most `skip` rows is
skipped. The first group with more rows keeps `card - skip` rows, or fewer when the limit
ends inside it; SQLite chooses which rows. Without a limit the later groups are kept. With a
limit the later groups get the rest of the limit. One group can be cut on both sides. -/
def window : Nat → Option Nat → Ranked α → ND (Ranked α)
  | _, _, [] => pure []
  | skip, keep, g :: gs =>
    if g.card ≤ skip then window (skip - g.card) keep gs
    else match keep with
      | none => do
        let kept ← g.take (g.card - skip)
        pure (kept :: gs)
      | some 0 => pure []
      | some (n + 1) => do
        let kept ← g.take (min (n + 1) (g.card - skip))
        let rest ← window 0 (some (n + 1 - min (n + 1) (g.card - skip))) gs
        pure (kept :: rest)

/-- For each offset `skip`, limit `keep` and ranking `r`: the lists that the window of `r`
permits are exactly the slices of the lists that `r` permits. The structural window agrees
with OFFSET and LIMIT applied to each list that SQLite may produce.
Proof sketch: induction on `r`. A skipped group shifts the offset. In a cut group, the lists
of a sub-bag of the right size are the middle slices of the arrangements of the group
(`Bag.take_bind_arrange`); the rest of the limit goes to the later groups. -/
theorem window_arrange (skip : Nat) (keep : Option Nat) (r : Ranked α) :
    (r.window skip keep >>= arrange) = (slice skip keep <$> r.arrange) := by
  induction r generalizing skip keep with
  | nil => exact ND.ext fun L => by cases keep <;> simp [window, slice]
  | cons g gs ih =>
    refine ND.ext fun L => ?_
    have card_of (l : List α) (hl : g.arrange l) : g.card = l.length := by rw [← hl]; rfl
    have short_case (keep : Option Nat) (short : g.card ≤ skip) :
        (window (skip - g.card) keep gs >>= arrange) L ↔
          (slice skip keep <$> arrange (g :: gs)) L := by
      have e (l m : List α) (hl : g.arrange l) :
          slice skip keep (l ++ m) = slice (skip - g.card) keep m := by
        rw [slice_append_of_length_le _ _ _ (card_of l hl ▸ short), card_of l hl]
      rw [ih]
      constructor
      · rintro ⟨m, hm, rfl⟩
        obtain ⟨l, hl⟩ := g.arrange_nonempty
        exact ⟨l ++ m, ⟨l, hl, m, hm, rfl⟩, (e l m hl).symm⟩
      · rintro ⟨_, ⟨l, hl, m, hm, rfl⟩, rfl⟩
        exact ⟨m, hm, e l m hl⟩
    match keep with
    | none =>
      rw [window]
      split
      · exact short_case none ‹_›
      have C := Bag.take_bind_arrange g skip (g.card - skip) (by omega)
      have e (l m : List α) (hl : g.arrange l) :
          slice skip none (l ++ m) = (l.drop skip).take (g.card - skip) ++ m := by
        rw [slice_none_append (l := l) skip m (by rw [← card_of l hl]; omega), card_of l hl]
      constructor
      · rintro ⟨_, ⟨kept, hk, rfl⟩, l₁, h₁, m, hm, rfl⟩
        obtain ⟨l, hl, rfl⟩ := (C l₁).mp ⟨kept, hk, h₁⟩
        exact ⟨l ++ m, ⟨l, hl, m, hm, rfl⟩, (e l m hl).symm⟩
      · rintro ⟨_, ⟨l, hl, m, hm, rfl⟩, rfl⟩
        obtain ⟨kept, hk, h₁⟩ := (C _).mpr ⟨l, hl, rfl⟩
        exact ⟨kept :: gs, ⟨kept, hk, rfl⟩, _, h₁, m, hm, e l m hl⟩
    | some 0 =>
      rw [window]
      split
      · exact short_case (some 0) ‹_›
      constructor
      · rintro ⟨_, rfl, rfl⟩
        obtain ⟨L₀, h₀⟩ := arrange_nonempty (g :: gs)
        exact ⟨L₀, h₀, (by simp [slice] : [] = slice skip (some 0) L₀)⟩
      · rintro ⟨L₀, _, rfl⟩
        exact ⟨[], rfl, (by simp [slice] : slice skip (some 0) L₀ = [])⟩
    | some (n + 1) =>
      rw [window]
      split
      · exact short_case (some (n + 1)) ‹_›
      have C := Bag.take_bind_arrange g skip (min (n + 1) (g.card - skip)) (by omega)
      have IH := congrFun (ih 0 (some (n + 1 - min (n + 1) (g.card - skip))))
      have e (l m : List α) (hl : g.arrange l) :
          slice skip (some (n + 1)) (l ++ m) = (l.drop skip).take (min (n + 1) (g.card - skip))
            ++ slice 0 (some (n + 1 - min (n + 1) (g.card - skip))) m := by
        rw [slice_some_append (l := l) skip (n + 1) m (by rw [← card_of l hl]; omega),
          card_of l hl]
      constructor
      · rintro ⟨_, ⟨kept, hk, rest, hrest, rfl⟩, l₁, h₁, m', hm', rfl⟩
        obtain ⟨l, hl, rfl⟩ := (C l₁).mp ⟨kept, hk, h₁⟩
        obtain ⟨m, hm, rfl⟩ := (IH m').mp ⟨rest, hrest, hm'⟩
        exact ⟨l ++ m, ⟨l, hl, m, hm, rfl⟩, (e l m hl).symm⟩
      · rintro ⟨_, ⟨l, hl, m, hm, rfl⟩, rfl⟩
        obtain ⟨kept, hk, h₁⟩ := (C _).mpr ⟨l, hl, rfl⟩
        obtain ⟨rest, hrest, hm'⟩ := (IH _).mpr ⟨m, hm, rfl⟩
        exact ⟨kept :: rest, ⟨kept, hk, rest, hrest, rfl⟩, _, h₁, _, hm', e l m hl⟩
#print axioms window_arrange

end Ranked

end BagResults
