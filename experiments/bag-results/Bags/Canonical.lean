import Bags.Ranked

/-!
# A canonical form for ranked rows

Two rankings can permit the same lists: `[{a}, {a}]` and `[{a, a}]` both permit only
`[a, a]`. The canonical form `Ranked.canon` drops empty groups and splits each group whose
rows are all equal into groups of one row. Two rankings permit the same lists exactly when
their canonical forms are equal (`arrange_eq_iff_canon`, in `Bags.CanonicalUnique`).
-/

namespace BagResults

namespace Ranked
variable {α : Type} [DecidableEq α]

/-- Whether all rows of a list are equal. -/
def allEqual (l : List α) : Bool := l.all fun x => l.all fun y => x == y

/-- For each list `l`: `allEqual l` holds if and only if all rows of `l` are equal. -/
theorem allEqual_iff (l : List α) : allEqual l = true ↔ ∀ x ∈ l, ∀ y ∈ l, x = y := by
  simp [allEqual]

omit [DecidableEq α] in
/-- For all lists `l` and `m`: if all rows of `l` are equal and `m` is a permutation of `l`,
then `m = l`. Such a list is determined by its bag. -/
theorem eq_of_perm_of_all_equal {l m : List α} (equal : ∀ x ∈ l, ∀ y ∈ l, x = y)
    (p : l.Perm m) : l = m := by
  cases l with
  | nil => exact p.nil_eq
  | cons a l' =>
    have hl : a :: l' = List.replicate (l'.length + 1) a :=
      List.eq_replicate_iff.mpr ⟨rfl, fun b hb => equal b hb a (by simp)⟩
    rw [hl] at p ⊢
    exact List.replicate_perm.mp p

/-- The canonical groups of a list of rows: one group of one row for each row when all rows
are equal (none for the empty list), else one group with all rows. -/
def canonGroupOfList (l : List α) : Ranked α :=
  if allEqual l then l.map fun x => Bag.ofList [x] else [Bag.ofList l]

/-- For all lists `l` and `m`: if `m` is a permutation of `l`, then they have the same
canonical groups. -/
theorem canonGroupOfList_perm {l m : List α} (p : l.Perm m) :
    canonGroupOfList l = canonGroupOfList m := by
  have same : allEqual l = allEqual m :=
    Bool.eq_iff_iff.mpr (by simp only [allEqual_iff, p.mem_iff])
  unfold canonGroupOfList
  rw [same]
  split
  · rename_i h
    rw [eq_of_perm_of_all_equal ((allEqual_iff l).mp (same ▸ h)) p]
  · rw [Bag.ofList_eq_iff.mpr p]

/-- The canonical groups of a tie group. -/
def canonGroup (g : Bag α) : Ranked α :=
  Quotient.lift canonGroupOfList (fun _ _ p => canonGroupOfList_perm p) g

/-- For each list `l`: the canonical groups of the bag of `l` are those of `l`. -/
@[simp] theorem canonGroup_ofList (l : List α) :
    canonGroup (Bag.ofList l) = canonGroupOfList l := rfl

/-- The canonical form of ranked rows: no empty groups, and a group whose rows are all equal
is split into groups of one row. -/
def canon (r : Ranked α) : Ranked α := List.flatMap canonGroup r

omit [DecidableEq α] in
/-- For each list `l`: the groups of one row for each row of `l` permit only `l`. -/
theorem arrange_singletons (l : List α) : arrange (l.map fun x => Bag.ofList [x]) = pure l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    refine ND.ext fun L => ?_
    simp [ih, Bag.ofList_eq_iff]

/-- For each group `g`: the canonical groups of `g` permit the arrangements of `g`. -/
theorem arrange_canonGroup (g : Bag α) : arrange (canonGroup g) = g.arrange := by
  obtain ⟨l, rfl⟩ := g.exists_ofList
  rw [canonGroup_ofList, canonGroupOfList]
  split
  · rename_i h
    rw [arrange_singletons]
    refine ND.ext fun L => ⟨fun e => by rw [(ND.pure_apply _ _).mp e]; rfl, fun e => ?_⟩
    exact (eq_of_perm_of_all_equal ((allEqual_iff l).mp h)
      (Bag.ofList_eq_iff.mp e).symm).symm
  · exact arrange_singleton _

/-- For each ranking `r`: the canonical form of `r` permits the same lists as `r`. -/
theorem arrange_canon (r : Ranked α) : r.canon.arrange = r.arrange := by
  induction r with
  | nil => rfl
  | cons g gs ih =>
    refine ND.ext fun L => ?_
    simp only [canon, List.flatMap_cons] at ih ⊢
    rw [arrange_append]
    simp only [arrange_canonGroup, ih, arrange_cons_apply]
    constructor
    · rintro ⟨l₁, l₂, h₁, h₂, rfl⟩; exact ⟨l₁, h₁, l₂, h₂, rfl⟩
    · rintro ⟨l₁, h₁, l₂, h₂, rfl⟩; exact ⟨l₁, l₂, h₁, h₂, rfl⟩
#print axioms arrange_canon

omit [DecidableEq α] in
/-- A tie group in canonical form: it has one row, or it has two different rows. -/
def GroupCanonical (g : Bag α) : Prop := g.card = 1 ∨ ∃ a ∈ g, ∃ b ∈ g, a ≠ b

/-- For each group `g`: every canonical group of `g` is in canonical form. -/
theorem canonGroup_canonical (g : Bag α) : ∀ h ∈ canonGroup g, GroupCanonical h := by
  obtain ⟨l, rfl⟩ := g.exists_ofList
  intro h hh
  rw [canonGroup_ofList, canonGroupOfList] at hh
  split at hh
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hh
    exact Or.inl rfl
  · rename_i ne
    rw [List.mem_singleton] at hh
    subst hh
    simp only [allEqual, List.all_eq_true, beq_iff_eq, Classical.not_forall] at ne
    obtain ⟨a, ha, b, hb, ab⟩ := ne
    exact Or.inr ⟨a, ha, b, hb, ab⟩

/-- For each ranking `r`: every group of the canonical form of `r` is in canonical form. -/
theorem canon_canonical (r : Ranked α) : ∀ h ∈ r.canon, GroupCanonical h := by
  intro h hh
  obtain ⟨g, _, hg⟩ := List.mem_flatMap.mp hh
  exact canonGroup_canonical g h hg
#print axioms canon_canonical

end Ranked

end BagResults
