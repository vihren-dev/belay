import Bags.Choice

/-!
# DISTINCT under a collation

DISTINCT keeps one row of each class of rows that a collation calls the same. When a class
holds different rows, for example 'a' and 'A' under NOCASE, the row that SQLite keeps depends
on the order of the rows. When the collation identifies only equal rows, DISTINCT is
deterministic.
-/

namespace BagResults

namespace Bag
variable {α : Type}

/-- One step of `firstOfEach`: keep `x` when no kept row is in the class of `x`. -/
def keepFirst (same : α → α → Bool) (kept : List α) (x : α) : List α :=
  if kept.any (same · x) then kept else kept ++ [x]

/-- One row of each class under `same`, in arrangement order: the first row of each class. -/
def firstOfEach (same : α → α → Bool) (l : List α) : List α :=
  l.foldl (keepFirst same) []

/-- DISTINCT under a collation: one row of each class. Which row SQLite keeps depends on the
arrangement that its plan produces. -/
def distinct (same : α → α → Bool) (b : Bag α) : ND (Bag α) :=
  (fun l => ofList (firstOfEach same l)) <$> b.arrange

/-- For each `same`, each set of rows `inside` on which `same` is equality, and all lists `l`
and `kept` of rows in `inside`: if `kept` has no duplicates, then the fold of `keepFirst`
over `l` from `kept` has no duplicates, and its members are the members of `kept` and of `l`.
Proof sketch: induction on `l`. A step keeps `x` only when no kept row equals `x`, so no
duplicate appears, and a step that skips `x` skips a row that is already kept. -/
theorem foldl_keepFirst (same : α → α → Bool) (inside : α → Prop)
    (identifies : ∀ x y, inside x → inside y → (same x y = true ↔ x = y)) :
    ∀ (l kept : List α), (∀ x ∈ kept, inside x) → (∀ x ∈ l, inside x) → kept.Nodup →
      (l.foldl (keepFirst same) kept).Nodup ∧
        ∀ a, a ∈ l.foldl (keepFirst same) kept ↔ a ∈ kept ∨ a ∈ l := by
  intro l
  induction l with
  | nil => intro kept _ _ nd; exact ⟨nd, fun a => by simp⟩
  | cons x l ih =>
    intro kept hk hl nd
    have hx : inside x := hl x (List.mem_cons_self ..)
    have step : (∀ y ∈ keepFirst same kept x, inside y) ∧ (keepFirst same kept x).Nodup ∧
        ∀ a, a ∈ keepFirst same kept x ↔ a ∈ kept ∨ a = x := by
      unfold keepFirst
      split
      · rename_i h
        obtain ⟨y, hy, hs⟩ := List.any_eq_true.mp h
        obtain rfl : y = x := (identifies y x (hk y hy) hx).mp hs
        exact ⟨hk, nd, fun a => ⟨Or.inl, fun h => h.elim id (· ▸ hy)⟩⟩
      · rename_i h
        have notin : x ∉ kept := fun m =>
          h (List.any_eq_true.mpr ⟨x, m, (identifies x x hx hx).mpr rfl⟩)
        refine ⟨fun y hy => ?_, ?_, fun a => by simp⟩
        · rcases List.mem_append.mp hy with m | m
          · exact hk y m
          · rw [List.mem_singleton.mp m]; exact hx
        · exact List.nodup_append.mpr ⟨nd, by simp, fun a ha b hb e =>
            notin (List.mem_singleton.mp hb ▸ e ▸ ha)⟩
    obtain ⟨hk', nd', mem'⟩ := step
    obtain ⟨ndr, memr⟩ := ih _ hk' (fun y hy => hl y (List.mem_cons_of_mem _ hy)) nd'
    refine ⟨ndr, fun a => ?_⟩
    rw [List.foldl_cons, memr, mem', List.mem_cons, or_assoc]

/-- For each `same` and bag `b`: if `same` is equality on the rows of `b`, then DISTINCT
under `same` on `b` is deterministic. -/
theorem distinct_deterministic (same : α → α → Bool) (b : Bag α)
    (identifies : ∀ x ∈ b, ∀ y ∈ b, same x y = true ↔ x = y) :
    ∃ c, b.distinct same = pure c := by
  obtain ⟨l, rfl⟩ := exists_ofList b
  have facts (m : List α) (pm : m.Perm l) := foldl_keepFirst same (· ∈ ofList l)
    (fun x y hx hy => identifies x hx y hy) m [] (by simp) (fun x hx => pm.mem_iff.mp hx)
    List.nodup_nil
  refine ⟨ofList (firstOfEach same l), ND.ext fun c => ⟨?_, fun e => ⟨l, rfl, e⟩⟩⟩
  rintro ⟨m, eq, rfl⟩
  have pm := ofList_eq_iff.mp eq
  obtain ⟨ndm, memm⟩ := facts m pm
  obtain ⟨ndl, meml⟩ := facts l (.refl l)
  refine ofList_eq_iff.mpr ((List.perm_ext_iff_of_nodup ndm ndl).mpr fun a => ?_)
  simp only [memm, meml, pm.mem_iff]
#print axioms distinct_deterministic

/-- For a type with a lawful `==` and each bag `b`: DISTINCT under `==` on `b` is
deterministic. -/
theorem distinct_beq_deterministic [BEq α] [LawfulBEq α] (b : Bag α) :
    ∃ c, b.distinct (· == ·) = pure c :=
  distinct_deterministic _ b fun _ _ _ _ => beq_iff_eq
#print axioms distinct_beq_deterministic

end Bag

end BagResults
