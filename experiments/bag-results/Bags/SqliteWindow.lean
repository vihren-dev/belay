import Bags.Window

/-!
# SQLite's integer LIMIT and OFFSET

In SQLite, LIMIT and OFFSET are integers. A negative LIMIT means no limit, and a negative
OFFSET means no offset. The adapters `sqliteLimit` and `sqliteOffset` map them to the
arguments of `Ranked.window`. The number of rows in the window is determined, even when the
rows are not (`card_window_sqlite`). Without ORDER BY, the rows of the window can be any
sub-bag of that size (`window_sqlite_ofBag_iff`).
-/

namespace BagResults
variable {α : Type}

/-- SQLite's LIMIT: a negative limit means no limit. -/
def sqliteLimit (limit : Int) : Option Nat := if limit < 0 then none else some limit.toNat

/-- SQLite's OFFSET: a negative offset means 0. -/
def sqliteOffset (offset : Int) : Nat := offset.toNat

/-- The number of rows that OFFSET `skip` and LIMIT `keep` take from `n` rows. -/
def sliceCount (skip : Nat) : Option Nat → Nat → Nat
  | none, n => n - skip
  | some k, n => min k (n - skip)

/-- For each window and list `l`: the slice of `l` has `sliceCount skip keep l.length`
rows. -/
theorem length_slice (skip : Nat) (keep : Option Nat) (l : List α) :
    (slice skip keep l).length = sliceCount skip keep l.length := by
  cases keep <;> simp [slice, sliceCount]

namespace Ranked

/-- For each ranking `w` and list `L` that `w` permits: `w` has `L.length` rows. -/
theorem card_toBag_of_arrange {w : Ranked α} {L : List α} (h : w.arrange L) :
    w.toBag.card = L.length := by
  rw [← (Bag.arrange_apply _ _).mp (arrange_toBag h)]
  rfl

/-- For each offset `skip`, limit `keep` and ranking `r`: every possible window of `r` has
`sliceCount skip keep (card r)` rows. The rows of the window are not determined, their
number is. -/
theorem card_window (skip : Nat) (keep : Option Nat) (r : Ranked α) :
    (fun w => w.toBag.card) <$> r.window skip keep = pure (sliceCount skip keep r.toBag.card) := by
  have law := congrFun (window_arrange skip keep r)
  refine ND.ext fun v => ⟨?_, ?_⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨L, hL⟩ := arrange_nonempty w
    obtain ⟨L₀, hL₀, e⟩ := (law L).mp ⟨w, hw, hL⟩
    have e' : L = slice skip keep L₀ := e
    show w.toBag.card = sliceCount skip keep r.toBag.card
    rw [card_toBag_of_arrange hL, card_toBag_of_arrange hL₀, e', length_slice]
  · rintro rfl
    obtain ⟨L₀, hL₀⟩ := arrange_nonempty r
    obtain ⟨w, hw, hL⟩ := (law _).mpr ⟨L₀, hL₀, rfl⟩
    refine ⟨w, hw, ?_⟩
    show sliceCount skip keep r.toBag.card = w.toBag.card
    rw [card_toBag_of_arrange hL, card_toBag_of_arrange hL₀, length_slice]
#print axioms card_window

/-- For all integers `offset` and `limit` and each ranking `r`: every window of `r` under
SQLite's OFFSET `offset` and LIMIT `limit` has a determined number of rows. For a negative
limit it is the number of rows after the offset, `card r - max offset 0`. Otherwise it is the
smaller of the limit and that number. -/
theorem card_window_sqlite (offset limit : Int) (r : Ranked α) :
    (fun w => w.toBag.card) <$> r.window (sqliteOffset offset) (sqliteLimit limit) =
      pure (if limit < 0 then r.toBag.card - offset.toNat
        else min limit.toNat (r.toBag.card - offset.toNat)) := by
  rw [card_window]
  unfold sqliteLimit sqliteOffset
  split <;> rfl
#print axioms card_window_sqlite

/-- For all integers `offset` and `limit` and each bag `b` without ORDER BY: the window of
`b` under SQLite's OFFSET and LIMIT has a determined number of rows: `card b - max offset 0`
for a negative limit, else the smaller of the limit and that number. -/
theorem card_window_sqlite_ofBag (offset limit : Int) (b : Bag α) :
    (fun w => w.toBag.card) <$> (ofBag b).window (sqliteOffset offset) (sqliteLimit limit) =
      pure (if limit < 0 then b.card - offset.toNat
        else min limit.toNat (b.card - offset.toNat)) := by
  have one : (ofBag b).toBag = b := Bag.append_nil b
  rw [card_window_sqlite, one]
#print axioms card_window_sqlite_ofBag

/-- For each offset `skip`, limit `keep` and all bags `b` and `c`: a window of the bag `b`
without ORDER BY can have the rows `c` if and only if `c` is a sub-bag of `b` with
`sliceCount skip keep (card b)` rows. OFFSET and LIMIT without ORDER BY keep any sub-bag of
that size of the rows.
Proof sketch: by the cases of `window` on one group. When the offset skips the group or the
limit is 0, the window has no group, its rows are the empty bag, and the count is 0; the
empty bag is the only sub-bag with no rows. In the other cases the window is one group, a
result of `Bag.take` with the count as its limit, and `Bag.take_iff` says that such a result is
a sub-bag with that number of rows. -/
theorem window_ofBag_iff (skip : Nat) (keep : Option Nat) (b c : Bag α) :
    (toBag <$> (ofBag b).window skip keep) c ↔ c.Sub b ∧ c.card = sliceCount skip keep b.card := by
  have empty (zero : sliceCount skip keep b.card = 0) :
      c = Bag.ofList [] ↔ c.Sub b ∧ c.card = sliceCount skip keep b.card := by
    rw [zero]
    constructor
    · rintro rfl
      exact ⟨⟨b, (Bag.nil_append b).symm⟩, rfl⟩
    · rintro ⟨_, h⟩
      obtain ⟨l, rfl⟩ := Bag.exists_ofList c
      rw [Bag.card_ofList, List.length_eq_zero_iff] at h
      rw [h]
  have kept (n : Nat) (count : min n b.card = sliceCount skip keep b.card) :
      (∃ k, b.take n k ∧ c = toBag [k]) ↔ c.Sub b ∧ c.card = sliceCount skip keep b.card := by
    have one (k : Bag α) : toBag [k] = k := Bag.append_nil k
    rw [← count]
    constructor
    · rintro ⟨k, hk, e⟩
      rw [e, one]
      exact (Bag.take_iff n b k).mp hk
    · intro h
      exact ⟨c, (Bag.take_iff n b c).mpr h, (one c).symm⟩
  unfold ofBag window
  split
  · rename_i short
    simp only [window, ND.map_apply, ND.pure_apply, exists_eq_left]
    refine empty ?_
    cases keep <;> simp [sliceCount] <;> omega
  · rename_i long
    cases keep with
    | none =>
      refine Iff.trans ?_ (kept (b.card - skip) (by simp [sliceCount]))
      simp only [ND.map_apply, ND.bind_apply, ND.pure_apply]
      constructor
      · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
        exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    | some k =>
      cases k with
      | zero =>
        simp only [ND.map_apply, ND.pure_apply, exists_eq_left]
        exact empty (by simp [sliceCount])
      | succ n =>
        refine Iff.trans ?_ (kept (min (n + 1) (b.card - skip)) (by simp [sliceCount]))
        simp only [window, ND.map_apply, ND.bind_apply, ND.pure_apply]
        constructor
        · rintro ⟨_, ⟨k, hk, _, rfl, rfl⟩, rfl⟩
          exact ⟨k, hk, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨_, ⟨k, hk, _, rfl, rfl⟩, rfl⟩
#print axioms window_ofBag_iff

/-- For all integers `offset` and `limit` and all bags `b` and `c`: a window of the bag `b`
without ORDER BY, under SQLite's OFFSET `offset` and LIMIT `limit`, can have the rows `c` if
and only if `c` is a sub-bag of `b` with this number of rows: `card b - max offset 0` for a
negative limit, else the smaller of the limit and that number. -/
theorem window_sqlite_ofBag_iff (offset limit : Int) (b c : Bag α) :
    (toBag <$> (ofBag b).window (sqliteOffset offset) (sqliteLimit limit)) c ↔
      c.Sub b ∧ c.card = (if limit < 0 then b.card - offset.toNat
        else min limit.toNat (b.card - offset.toNat)) := by
  rw [window_ofBag_iff]
  unfold sqliteLimit sqliteOffset
  split <;> rfl
#print axioms window_sqlite_ofBag_iff

end Ranked

end BagResults
