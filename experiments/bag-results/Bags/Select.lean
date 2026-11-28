import Bags.Equivalence
import Bags.Window

/-!
# A single-table SELECT

The pipeline of a single-table SELECT in SQLite's order of clauses: WHERE, ORDER BY, the
window, then the projection. The theorems show that the pipeline composes with the algebra
of bags.
-/

namespace BagResults
variable {ρ ο : Type}

/-- A single-table SELECT in SQLite's order of clauses: WHERE `keep`, ORDER BY `le`, OFFSET
`skip`, LIMIT `limit`, then the projection `project`. -/
def select (keep : ρ → Bool) (le : ρ → ρ → Bool) (skip : Nat) (limit : Option Nat)
    (project : ρ → ο) (rows : Bag ρ) : ND (Ranked ο) := do
  let ranked ← Ranked.rank le (rows.filter keep)
  let windowed ← ranked.window skip limit
  pure (windowed.map project)

/-- For all conditions `keep₁` and `keep₂` and every other clause: a SELECT with WHERE
`keep₁` over the rows that satisfy `keep₂` is the SELECT with WHERE `keep₂ x && keep₁ x`
over all rows. -/
theorem select_filter (keep₁ keep₂ : ρ → Bool) (le : ρ → ρ → Bool) (skip : Nat)
    (limit : Option Nat) (project : ρ → ο) (rows : Bag ρ) :
    select keep₁ le skip limit project (rows.filter keep₂) =
      select (fun x => keep₂ x && keep₁ x) le skip limit project rows := by
  simp only [select, Bag.filter_filter]
#print axioms select_filter

/-- For each WHERE `keep`, order `le`, projection `project` and bag `rows`: if `le x y` holds
for all kept rows `x` and `y`, then the SELECT without OFFSET and LIMIT is equivalent to the
deterministic result with the one group of the projected kept rows.
Proof sketch: a list of the result is the projection of a list of a ranking in the window.
With no OFFSET and no LIMIT the window permits the lists of the ranking
(`window_arrange`). The ranking is one group, so it permits the arrangements of the kept
rows (`rank_arrange_of_all_tie`), and their projections are the arrangements of the
projected bag (`Bag.arrange_map`). -/
theorem select_unordered (keep : ρ → Bool) (le : ρ → ρ → Bool) (project : ρ → ο)
    (rows : Bag ρ) (all_tie : ∀ x ∈ rows.filter keep, ∀ y ∈ rows.filter keep, le x y = true) :
    Equivalent (select keep le 0 none project rows)
      (pure (Ranked.ofBag ((rows.filter keep).map project))) := by
  have ranked := congrFun (Ranked.rank_arrange_of_all_tie le _ all_tie)
  have windowed (r : Ranked ρ) := congrFun (Ranked.window_arrange 0 none r)
  have projected (w : Ranked ρ) := congrFun (Ranked.arrange_map project w)
  have bag := congrFun (Bag.arrange_map project (rows.filter keep))
  unfold Equivalent
  rw [observe_pure, Ranked.ofBag, Ranked.arrange_singleton]
  refine ND.ext fun L => ?_
  rw [bag]
  constructor
  · rintro ⟨_, ⟨r, hr, w, hw, rfl⟩, hL⟩
    obtain ⟨L', hL', rfl⟩ := (projected w L).mp hL
    obtain ⟨L₀, hL₀, e⟩ := (windowed r L').mp ⟨w, hw, hL'⟩
    obtain rfl : L' = L₀ := e
    exact ⟨L', (ranked L').mp ⟨r, hr, hL₀⟩, rfl⟩
  · rintro ⟨L₀, hL₀, rfl⟩
    obtain ⟨r, hr, hr₀⟩ := (ranked L₀).mpr hL₀
    obtain ⟨w, hw, hw₀⟩ := (windowed r L₀).mpr ⟨L₀, hr₀, (List.drop_zero ..).symm⟩
    exact ⟨_, ⟨r, hr, w, hw, rfl⟩, (projected w _).mpr ⟨L₀, hw₀, rfl⟩⟩
#print axioms select_unordered

/-- For each WHERE `keep`, projection `project` and bag `rows`: a SELECT without ORDER BY,
OFFSET and LIMIT is equivalent to the deterministic bag of the projected kept rows. -/
theorem select_without_order (keep : ρ → Bool) (project : ρ → ο) (rows : Bag ρ) :
    Equivalent (select keep (fun _ _ => true) 0 none project rows)
      (pure (Ranked.ofBag ((rows.filter keep).map project))) :=
  select_unordered keep _ project rows fun _ _ _ _ => rfl
#print axioms select_without_order

end BagResults
