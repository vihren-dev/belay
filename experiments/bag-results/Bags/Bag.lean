import Bags.ND

/-!
# Bags of rows

SQLite does not promise an order for the rows of a query without ORDER BY. Such rows form a
bag: a list up to permutation. This file defines bags and the operations that relational
algebra applies to them.
-/

namespace BagResults

/-- Rows whose order SQLite does not promise: lists up to permutation. -/
def Bag (α : Type) : Type := Quotient (List.isSetoid α)

namespace Bag
variable {α β : Type}

/-- The bag of the rows of a list. -/
def ofList (l : List α) : Bag α := Quotient.mk _ l

/-- For all lists `l` and `m`: the bags of `l` and `m` are equal if and only if `m` is a
permutation of `l`. -/
theorem ofList_eq_iff {l m : List α} : ofList l = ofList m ↔ l.Perm m :=
  ⟨Quotient.exact, fun p => Quotient.sound p⟩
#print axioms ofList_eq_iff

/-- For each bag `b` there is a list `l` whose bag is `b`. -/
theorem exists_ofList (b : Bag α) : ∃ l, ofList l = b := Quotient.exists_rep b

/-- To prove a property of every bag, it is sufficient to prove it for the bag of every
list. -/
@[elab_as_elim] theorem induction_on {motive : Bag α → Prop} (b : Bag α)
    (of_list : ∀ l, motive (ofList l)) : motive b :=
  Quotient.inductionOn b of_list

/-- The number of rows. -/
def card : Bag α → Nat := Quotient.lift List.length fun _ _ p => p.length_eq

/-- For each list `l`: the bag of `l` has as many rows as `l`. -/
@[simp] theorem card_ofList (l : List α) : card (ofList l) = l.length := rfl

/-- The rows mapped one by one: a projection. -/
def map (f : α → β) : Bag α → Bag β :=
  Quotient.lift (fun l => ofList (l.map f)) fun _ _ p => Quotient.sound (p.map f)

/-- For each `f` and list `l`: the map of the bag of `l` is the bag of the map of `l`. -/
@[simp] theorem map_ofList (f : α → β) (l : List α) : map f (ofList l) = ofList (l.map f) :=
  rfl

/-- The rows that satisfy a condition: WHERE. -/
def filter (p : α → Bool) : Bag α → Bag α :=
  Quotient.lift (fun l => ofList (l.filter p)) fun _ _ s => Quotient.sound (s.filter p)

/-- For each `p` and list `l`: the filter of the bag of `l` is the bag of the filter of `l`. -/
@[simp] theorem filter_ofList (p : α → Bool) (l : List α) :
    filter p (ofList l) = ofList (l.filter p) := rfl

/-- The rows of both bags: UNION ALL. -/
def append : Bag α → Bag α → Bag α :=
  Quotient.lift₂ (fun l m => ofList (l ++ m)) fun _ _ _ _ p q => Quotient.sound (p.append q)

/-- `b ++ c` is UNION ALL of the bags `b` and `c`. -/
instance : Append (Bag α) := ⟨append⟩

/-- For all lists `l` and `m`: the union of their bags is the bag of `l ++ m`. -/
@[simp] theorem ofList_append (l m : List α) : ofList l ++ ofList m = ofList (l ++ m) := rfl

/-- For all lists `l`, `m`, `m'` with `m` a permutation of `m'`: the pairs of `l` with `m`
are a permutation of the pairs of `l` with `m'`. -/
private theorem perm_pairs {m m' : List β} (q : m.Perm m') (l : List α) :
    (l.flatMap fun x => m.map (x, ·)).Perm (l.flatMap fun x => m'.map (x, ·)) := by
  induction l with
  | nil => exact .refl _
  | cons x l ih => simpa [List.flatMap_cons] using (q.map _).append ih

/-- Every pair of rows: a join before its condition. -/
def product : Bag α → Bag β → Bag (α × β) :=
  Quotient.lift₂ (fun l m => ofList (l.flatMap fun x => m.map (x, ·)))
    fun _ _ _ _ p q => Quotient.sound ((p.flatMap_right _).trans (perm_pairs q _))

/-- For all lists `l` and `m`: the product of their bags is the bag of all pairs of a row of
`l` and a row of `m`. -/
@[simp] theorem product_ofList (l : List α) (m : List β) :
    product (ofList l) (ofList m) = ofList (l.flatMap fun x => m.map (x, ·)) := rfl

/-- A row is a member of a bag when it is a member of a list of the bag. -/
instance : Membership α (Bag α) :=
  ⟨fun b a => Quotient.lift (fun l => a ∈ l) (fun _ _ (p : List.Perm _ _) => propext p.mem_iff) b⟩

/-- For each row `a` and list `l`: `a` is in the bag of `l` if and only if `a` is in `l`. -/
@[simp] theorem mem_ofList {a : α} {l : List α} : a ∈ ofList l ↔ a ∈ l := Iff.rfl

/-- Equality of bags is decidable when equality of rows is decidable. The instance compares
two lists of the bags with `List.isPerm`. -/
instance [DecidableEq α] : DecidableEq (Bag α) := fun b c =>
  Quotient.recOnSubsingleton₂ b c fun l m =>
    decidable_of_iff (l.isPerm m) (List.isPerm_iff.trans ofList_eq_iff.symm)

end Bag

end BagResults
