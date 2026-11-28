import Bags.Bag

/-!
# The sample of a bag

A bag has no order. For a type with a total order, each bag has one sorted list of its rows:
its sample. `Bag.sample` computes it from the bag. The model can use it to show a bag, to
decide the equality of two bags by the sort of a list of each and a comparison of the sorted
lists, and to list the choices of a bag in a fixed order. The sample is not an order that SQLite promises: a claim
about the sample is a claim about the sorted rows.

The sort is the insertion sort of the model (`stableSort`), with the same laws. It uses only
structural recursion, so the kernel can evaluate it. `List.mergeSort` uses well-founded
recursion, and `decide` does not reduce it.
-/

namespace BagResults

variable {α : Type}

/-- Insert `item` after each leading row `head` with `le head item`. In a sorted list, the item
goes after its equals. -/
def insertStable (le : α → α → Bool) (item : α) : List α → List α
  | [] => [item]
  | head :: tail => if le head item then head :: insertStable le item tail else item :: head :: tail

/-- The insertion sort by `le`: each row, in list order, goes after its equals. -/
def stableSort (le : α → α → Bool) (items : List α) : List α :=
  items.foldl (fun sorted item => insertStable le item sorted) []

/-- For each `le`, row `item` and list `items`: the insertion of `item` into `items` is a
permutation of `item :: items`.
Proof sketch: induction on `items`; when the item goes after the head, one swap moves it to the
front. -/
theorem insertStable_perm (le : α → α → Bool) (item : α) :
    ∀ items : List α, (insertStable le item items).Perm (item :: items)
  | [] => .refl _
  | head :: tail => by
    unfold insertStable
    split
    · exact ((insertStable_perm le item tail).cons head).trans (.swap item head tail)
    · exact .refl _

/-- For each `le` and all lists `items` and `start`: the insertion of the rows of `items`, one
by one, into `start` gives a permutation of `start ++ items`.
Proof sketch: induction on `items`, for each `start`; each insertion is a permutation of the row
in front of `start`, and moving the row to the middle is a permutation too. -/
theorem foldl_insertStable_perm (le : α → α → Bool) : ∀ (items start : List α),
    (items.foldl (fun sorted item => insertStable le item sorted) start).Perm (start ++ items)
  | [], start => by simp
  | item :: items, start => by
    simp only [List.foldl_cons]
    refine (foldl_insertStable_perm le items _).trans ?_
    exact ((insertStable_perm le item start).append_right items).trans List.perm_middle.symm

/-- For each `le` and list `items`: the sort of `items` is a permutation of `items`.
Proof sketch: the sort inserts the rows into the empty list, so the previous law applies. -/
theorem stableSort_perm (le : α → α → Bool) (items : List α) :
    (stableSort le items).Perm items := by
  simpa [stableSort] using foldl_insertStable_perm le items []
#print axioms stableSort_perm

/-- For each transitive and total `le`, row `item` and list `items` sorted by `le`: the
insertion of `item` into `items` is sorted by `le`.
Proof sketch: induction on `items`. When the item goes after the head, the head is at most the
item and each later row. When it goes before the head, totality puts the item at most the
head, and transitivity at most each later row. -/
theorem insertStable_sorted (le : α → α → Bool) (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (item : α) :
    ∀ items : List α, items.Pairwise (le · ·) → (insertStable le item items).Pairwise (le · ·)
  | [], _ => by simp [insertStable]
  | head :: tail, sorted => by
    rw [List.pairwise_cons] at sorted
    unfold insertStable
    split
    · rename_i before
      refine List.pairwise_cons.2
        ⟨fun x member => ?_, insertStable_sorted le trans total item tail sorted.2⟩
      rcases List.mem_cons.1 ((insertStable_perm le item tail).mem_iff.1 member) with equal | later
      · exact equal ▸ before
      · exact sorted.1 x later
    · rename_i after
      have first : le item head := by simpa [after] using total head item
      refine List.pairwise_cons.2 ⟨fun x member => ?_, List.pairwise_cons.2 sorted⟩
      rcases List.mem_cons.1 member with equal | later
      · exact equal ▸ first
      · exact trans _ _ _ first (sorted.1 x later)

/-- For each transitive and total `le` and list `items`: the sort of `items` is sorted by
`le`.
Proof sketch: the empty list is sorted, and each insertion keeps the order. -/
theorem stableSort_sorted (le : α → α → Bool) (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (items : List α) :
    (stableSort le items).Pairwise (le · ·) := by
  suffices ∀ (items start : List α), start.Pairwise (le · ·) →
      (items.foldl (fun sorted item => insertStable le item sorted) start).Pairwise (le · ·) from
    this items [] .nil
  intro items
  induction items with
  | nil => exact fun _ sorted => sorted
  | cons item items ih =>
    exact fun start sorted => ih _ (insertStable_sorted le trans total item start sorted)
#print axioms stableSort_sorted

/-- A Boolean order with exactly one sorted permutation of each list. -/
structure SortOrder (α : Type) where
  /-- `le a b`: `a` can come before `b`. -/
  le : α → α → Bool
  /-- For all `a` and `b`: `le a b` or `le b a`. -/
  total : ∀ a b, le a b || le b a
  /-- For all `a`, `b` and `c`: if `le a b` and `le b c`, then `le a c`. -/
  trans : ∀ a b c, le a b → le b c → le a c
  /-- For all `a` and `b`: if `le a b` and `le b a`, then `a = b`. -/
  antisymm : ∀ a b, le a b → le b a → a = b

/-- For each sort order `o` and all lists `l` and `m`: if `l` is a permutation of `m`, then
the sorts of `l` and `m` are equal.
Proof sketch: the two sorts are sorted permutations of each other, and an antisymmetric order
has only one sorted permutation of a list (`List.Perm.eq_of_pairwise`). -/
theorem SortOrder.stableSort_eq_of_perm (o : SortOrder α) {l m : List α} (p : l.Perm m) :
    stableSort o.le l = stableSort o.le m :=
  List.Perm.eq_of_pairwise (fun a b _ _ => o.antisymm a b)
    (stableSort_sorted o.le o.trans o.total l) (stableSort_sorted o.le o.trans o.total m)
    (((stableSort_perm o.le l).trans p).trans (stableSort_perm o.le m).symm)
#print axioms SortOrder.stableSort_eq_of_perm

namespace Bag

/-- The sample of a bag: its rows sorted by `o`. -/
def sample (o : SortOrder α) : Bag α → List α :=
  Quotient.lift (stableSort o.le) fun _ _ p => o.stableSort_eq_of_perm p

/-- For each sort order `o` and list `l`: the sample of the bag of `l` is the sort of `l`. -/
@[simp] theorem sample_ofList (o : SortOrder α) (l : List α) :
    (ofList l).sample o = stableSort o.le l := rfl

/-- For each sort order `o` and bag `b`: the bag of the sample of `b` is `b`.
Proof sketch: the sample of the bag of `l` is the sort of `l`, a permutation of `l`. -/
theorem ofList_sample (o : SortOrder α) (b : Bag α) : ofList (b.sample o) = b := by
  induction b using induction_on with
  | of_list l => exact ofList_eq_iff.mpr (stableSort_perm o.le l)
#print axioms ofList_sample

/-- For each sort order `o` and all bags `b` and `c`: `b` and `c` have the same sample if and
only if `b = c`.
Proof sketch: each bag is the bag of its sample, so equal samples give equal bags. -/
theorem sample_eq_iff (o : SortOrder α) (b c : Bag α) : b.sample o = c.sample o ↔ b = c :=
  ⟨fun same => by rw [← ofList_sample o b, same, ofList_sample], fun same => same ▸ rfl⟩
#print axioms sample_eq_iff

/-- The equality of bags, decided through their samples. A type with a sort order can use it
as its instance. The kernel then sorts a list of each bag and compares the sorted lists. -/
def decEqBySample [DecidableEq α] (o : SortOrder α) : DecidableEq (Bag α) := fun b c =>
  decidable_of_iff (b.sample o = c.sample o) (sample_eq_iff o b c)

end Bag

end BagResults
