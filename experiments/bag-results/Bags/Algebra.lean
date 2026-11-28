import Bags.Bag

/-!
# The algebra of bags

The laws that a query rewriter uses to move WHERE, projections and UNION ALL. Each law holds
for every bag, so a rewrite with it never changes the rows of a result.
-/

namespace BagResults

namespace Bag
variable {α β γ : Type}

/-- For all conditions `p` and `q` and each bag `b`: a filter by `p` and then a filter by `q`
is one filter by `p x && q x`. -/
theorem filter_filter (p q : α → Bool) (b : Bag α) :
    (b.filter p).filter q = b.filter (fun x => p x && q x) := by
  induction b using induction_on with
  | of_list l => simp only [filter_ofList, List.filter_filter, Bool.and_comm]
#print axioms filter_filter

/-- For all functions `f` and `g` and each bag `b`: a map by `f` and then a map by `g` is one
map by `g ∘ f`. -/
theorem map_map (f : α → β) (g : β → γ) (b : Bag α) : (b.map f).map g = b.map (g ∘ f) := by
  induction b using induction_on with
  | of_list l => simp only [map_ofList, List.map_map]
#print axioms map_map

/-- For each function `f`, condition `p` and bag `b`: a filter by `p` after a map by `f` is a
filter by `p ∘ f` before the map. -/
theorem filter_map (f : α → β) (p : β → Bool) (b : Bag α) :
    (b.map f).filter p = (b.filter (p ∘ f)).map f := by
  induction b using induction_on with
  | of_list l => simp only [map_ofList, filter_ofList, List.filter_map]
#print axioms filter_map

/-- For each condition `p` and all bags `b` and `c`: a filter of a union is the union of the
filters. -/
theorem filter_append (p : α → Bool) (b c : Bag α) :
    (b ++ c).filter p = b.filter p ++ c.filter p := by
  induction b using induction_on with
  | of_list l => induction c using induction_on with
    | of_list m => simp only [ofList_append, filter_ofList, List.filter_append]
#print axioms filter_append

/-- For each function `f` and all bags `b` and `c`: a map of a union is the union of the
maps. -/
theorem map_append (f : α → β) (b c : Bag α) : (b ++ c).map f = b.map f ++ c.map f := by
  induction b using induction_on with
  | of_list l => induction c using induction_on with
    | of_list m => simp only [ofList_append, map_ofList, List.map_append]
#print axioms map_append

/-- For all bags `b` and `c`: UNION ALL is commutative, `b ++ c = c ++ b`. -/
theorem append_comm (b c : Bag α) : b ++ c = c ++ b := by
  induction b using induction_on with
  | of_list l => induction c using induction_on with
    | of_list m => exact ofList_eq_iff.mpr List.perm_append_comm
#print axioms append_comm

/-- For all bags `b`, `c` and `d`: UNION ALL is associative. -/
theorem append_assoc (b c d : Bag α) : b ++ c ++ d = b ++ (c ++ d) := by
  induction b using induction_on with
  | of_list l => induction c using induction_on with
    | of_list m => induction d using induction_on with
      | of_list n => simp only [ofList_append, List.append_assoc]
#print axioms append_assoc

/-- For each bag `b`: the empty bag is a unit of UNION ALL on the left. -/
@[simp] theorem nil_append (b : Bag α) : ofList [] ++ b = b := by
  induction b using induction_on with
  | of_list l => rfl

/-- For each bag `b`: the empty bag is a unit of UNION ALL on the right. -/
@[simp] theorem append_nil (b : Bag α) : b ++ ofList [] = b := by
  rw [append_comm, nil_append]

/-- For all bags `b` and `c`: the union has `card b + card c` rows. -/
@[simp] theorem card_append (b c : Bag α) : (b ++ c).card = b.card + c.card := by
  induction b using induction_on with
  | of_list l => induction c using induction_on with
    | of_list m => simp only [ofList_append, card_ofList, List.length_append]

/-- For each function `f` and bag `b`: a map keeps the number of rows. -/
@[simp] theorem card_map (f : α → β) (b : Bag α) : (b.map f).card = b.card := by
  induction b using induction_on with
  | of_list l => simp only [map_ofList, card_ofList, List.length_map]

/-- For each condition `p` and bag `b`: a filter does not add rows. -/
theorem card_filter_le (p : α → Bool) (b : Bag α) : (b.filter p).card ≤ b.card := by
  induction b using induction_on with
  | of_list l => exact List.length_filter_le p l
#print axioms card_filter_le

/-- For all lists `l` and `m` and tests `p` and `q`: the pairs of `l` with `m` whose first part
passes `p` and whose second part passes `q` are the pairs of `l.filter p` with `m.filter q`,
in the same order. -/
private theorem filter_pairs (p : α → Bool) (q : β → Bool) (l : List α) (m : List β) :
    (l.flatMap fun x => m.map (x, ·)).filter (fun pr => p pr.1 && q pr.2) =
      (l.filter p).flatMap fun x => (m.filter q).map (x, ·) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases hx : p x <;>
      simp [List.flatMap_cons, List.filter_append, List.filter_map, hx, ih, Function.comp_def]

/-- For all conditions `p` on the left rows and `q` on the right rows, and all bags `b` and
`c`: a filter of the product by `p` on the left component and `q` on the right component is
the product of the filtered bags. A join condition that splits into a condition on each side
can move below the join. -/
theorem filter_product (p : α → Bool) (q : β → Bool) (b : Bag α) (c : Bag β) :
    (b.product c).filter (fun pr => p pr.1 && q pr.2) = (b.filter p).product (c.filter q) := by
  induction b using induction_on with
  | of_list l => induction c using induction_on with
    | of_list m => simp only [product_ofList, filter_ofList, filter_pairs]
#print axioms filter_product

/-- For each condition `p` on the left rows and all bags `b` and `c`: a filter of the product
by `p` on the left component is the product of the filtered left bag with `c`. -/
theorem filter_product_left (p : α → Bool) (b : Bag α) (c : Bag β) :
    (b.product c).filter (fun pr => p pr.1) = (b.filter p).product c := by
  have h := filter_product p (fun _ => true) b c
  induction c using induction_on with
  | of_list m => simpa [List.filter_eq_self.mpr fun _ _ => rfl] using h

/-- For each condition `q` on the right rows and all bags `b` and `c`: a filter of the product
by `q` on the right component is the product of `b` with the filtered right bag. -/
theorem filter_product_right (q : β → Bool) (b : Bag α) (c : Bag β) :
    (b.product c).filter (fun pr => q pr.2) = b.product (c.filter q) := by
  have h := filter_product (fun _ => true) q b c
  induction b using induction_on with
  | of_list l => simpa [List.filter_eq_self.mpr fun _ _ => rfl] using h

/-- For all bags `b` and `c`: the product has `card b * card c` rows. -/
theorem card_product (b : Bag α) (c : Bag β) : (b.product c).card = b.card * c.card := by
  induction b using induction_on with
  | of_list l => induction c using induction_on with
    | of_list m =>
      simp only [product_ofList, card_ofList]
      induction l with
      | nil => simp
      | cons x l ih => simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]
#print axioms card_product

end Bag

end BagResults
