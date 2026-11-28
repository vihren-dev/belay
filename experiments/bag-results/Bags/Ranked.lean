import Bags.Arrange

/-!
# Ranked rows

ORDER BY ranks a bag into tie groups. The groups are in order, and the rows of one group are
a bag: SQLite may produce them in any order. A query without ORDER BY has one group.
-/

namespace BagResults

/-- Rows in the order of ORDER BY: tie groups in order, each a bag. -/
abbrev Ranked (α : Type) := List (Bag α)

namespace Ranked
variable {α β : Type}

/-- A bag as one tie group: a query without ORDER BY. -/
def ofBag (b : Bag α) : Ranked α := [b]

/-- The rows without their order: a subquery read as a source. -/
def toBag (r : Ranked α) : Bag α := r.foldr (· ++ ·) (Bag.ofList [])

/-- The rows mapped one by one: a projection after ORDER BY keeps the tie groups. -/
def map (f : α → β) (r : Ranked α) : Ranked β := List.map (Bag.map f) r

/-- The lists in which SQLite may produce the rows: each group in some order, the groups in
their order. -/
def arrange : Ranked α → ND (List α)
  | [] => pure []
  | g :: gs => do
    let l ← g.arrange
    let m ← arrange gs
    pure (l ++ m)

/-- For each list `l`: the ranking without groups permits `l` if and only if `l` is empty. -/
@[simp] theorem arrange_nil_apply (l : List α) : arrange ([] : Ranked α) l ↔ l = [] := Iff.rfl

/-- For each group `g`, groups `gs` and list `l`: `g :: gs` permits `l` if and only if `l` is
an arrangement of `g` followed by a list that `gs` permits. -/
@[simp] theorem arrange_cons_apply (g : Bag α) (gs : Ranked α) (l : List α) :
    arrange (g :: gs) l ↔ ∃ l₁, g.arrange l₁ ∧ ∃ l₂, arrange gs l₂ ∧ l = l₁ ++ l₂ := Iff.rfl

/-- For each bag `g`: the ranking with the one group `g` permits the arrangements of `g`. -/
theorem arrange_singleton (g : Bag α) : arrange [g] = g.arrange :=
  ND.ext fun l => by simp

/-- For all rankings `r` and `r'` and each list `l`: `r ++ r'` permits `l` if and only if
`l` is a list that `r` permits followed by a list that `r'` permits. -/
theorem arrange_append (r r' : Ranked α) (l : List α) :
    arrange (r ++ r') l ↔ ∃ l₁ l₂, arrange r l₁ ∧ arrange r' l₂ ∧ l = l₁ ++ l₂ := by
  induction r generalizing l with
  | nil => exact ⟨fun h => ⟨[], l, rfl, h, rfl⟩, fun ⟨_, _, e, h, el⟩ => by subst e el; exact h⟩
  | cons g gs ih =>
    simp only [List.cons_append, arrange_cons_apply, ih]
    constructor
    · rintro ⟨a, ha, _, ⟨m₁, m₂, hm₁, hm₂, rfl⟩, rfl⟩
      exact ⟨a ++ m₁, m₂, ⟨a, ha, m₁, hm₁, rfl⟩, hm₂, (List.append_assoc ..).symm⟩
    · rintro ⟨_, m₂, ⟨a, ha, m₁, hm₁, rfl⟩, hm₂, rfl⟩
      exact ⟨a, ha, m₁ ++ m₂, ⟨m₁, m₂, hm₁, hm₂, rfl⟩, List.append_assoc ..⟩
#print axioms arrange_append

/-- For each ranking `r`: `r` permits at least one list. -/
theorem arrange_nonempty (r : Ranked α) : ∃ l, r.arrange l := by
  induction r with
  | nil => exact ⟨[], rfl⟩
  | cons g gs ih =>
    obtain ⟨l₁, h₁⟩ := g.arrange_nonempty
    obtain ⟨l₂, h₂⟩ := ih
    exact ⟨l₁ ++ l₂, l₁, h₁, l₂, h₂, rfl⟩

/-- For each ranking `r` and list `l`: if `r` permits `l`, then `l` is an arrangement of the
bag of all rows of `r`. -/
theorem arrange_toBag {r : Ranked α} {l : List α} (h : r.arrange l) : r.toBag.arrange l := by
  induction r generalizing l with
  | nil => rw [(arrange_nil_apply l).mp h]; rfl
  | cons g gs ih =>
    obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := h
    simp only [Bag.arrange_apply] at h₁ ih ⊢
    rw [← Bag.ofList_append, h₁, ih h₂]
    rfl
#print axioms arrange_toBag

/-- For each function `f` and ranking `r`: the lists of the mapped ranking are the maps of the
lists of `r`. A projection commutes with the choice of an order. -/
theorem arrange_map (f : α → β) (r : Ranked α) :
    (r.map f).arrange = List.map f <$> r.arrange := by
  induction r with
  | nil => exact ND.ext fun l => by simp [map]
  | cons g gs ih =>
    refine ND.ext fun L => ?_
    have hg := congrFun (Bag.arrange_map f g)
    have hgs := congrFun ih
    simp only [map, List.map_cons, arrange_cons_apply, ND.map_apply] at hg hgs ⊢
    constructor
    · rintro ⟨l₁, h₁, l₂, h₂, rfl⟩
      obtain ⟨a, ha, rfl⟩ := (hg l₁).mp h₁
      obtain ⟨m, hm, rfl⟩ := (hgs l₂).mp h₂
      exact ⟨a ++ m, ⟨a, ha, m, hm, rfl⟩, (List.map_append ..).symm⟩
    · rintro ⟨_, ⟨a, ha, m, hm, rfl⟩, rfl⟩
      exact ⟨_, (hg _).mpr ⟨a, ha, rfl⟩, _, (hgs _).mpr ⟨m, hm, rfl⟩, List.map_append ..⟩
#print axioms arrange_map

end Ranked

end BagResults
