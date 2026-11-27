import Std

set_option doc.verso true

/-! Relations between Boolean row filters on one input. For a SQL condition, the filter
returns true exactly when the WHERE clause accepts the row. Its Boolean complement therefore
includes rows for which the SQL condition evaluates to NULL. -/

namespace Belay.Sqlite.Model.RowFilter

variable {α : Type u}

/-- Every input row accepted by the first filter is also accepted by the second. -/
def ImpliesOn (rows : List α) (p q : α → Bool) : Prop :=
  ∀ row ∈ rows, p row = true → q row = true

/-- The two filters accept exactly the same rows of this input. -/
def AgreeOn (rows : List α) (p q : α → Bool) : Prop :=
  ∀ row ∈ rows, p row = q row

/-- The filter rejects every row in the input. -/
def EmptyOn (rows : List α) (p : α → Bool) : Prop :=
  ∀ row ∈ rows, p row = false

/-- No row in the input passes both filters. -/
def DisjointOn (rows : List α) (p q : α → Bool) : Prop :=
  ∀ row ∈ rows, p row = true → q row = false

/-- For any input and filters, implication holds exactly when no row passes the first filter
and fails the second. Proof sketch: expand the Boolean test for a counterexample. -/
theorem impliesOn_iff_no_counterexample (rows : List α) (p q : α → Bool) :
    ImpliesOn rows p q ↔ EmptyOn rows (fun row => p row && !q row) := by
  simp [ImpliesOn, EmptyOn]

/-- For any input and filters, implication holds exactly when every member of the first
filtered list occurs in the second. Proof sketch: use membership in a filtered list in both directions. -/
theorem impliesOn_iff_subset (rows : List α) (p q : α → Bool) :
    ImpliesOn rows p q ↔ rows.filter p ⊆ rows.filter q := by
  constructor
  · intro h row member
    obtain ⟨seen, kept⟩ := List.mem_filter.mp member
    exact List.mem_filter.mpr ⟨seen, h row seen kept⟩
  · intro h row seen kept
    exact (List.mem_filter.mp (h (List.mem_filter.mpr ⟨seen, kept⟩))).2

/-- For any input and filters, agreement holds exactly when the two filtered lists are equal,
including order and repetitions. Proof sketch: agreement preserves filtering. In the reverse
direction, a row kept on either side occurs on the other side. -/
theorem agreeOn_iff_filter_eq (rows : List α) (p q : α → Bool) :
    AgreeOn rows p q ↔ rows.filter p = rows.filter q := by
  refine ⟨List.filter_congr, fun eq row seen => Bool.eq_iff_iff.mpr ?_⟩
  exact ⟨(impliesOn_iff_subset ..).mpr (eq ▸ List.Subset.refl _) row seen,
    (impliesOn_iff_subset ..).mpr (eq.symm ▸ List.Subset.refl _) row seen⟩

/-- For any input and filter, the filter rejects every input row exactly when filtering gives
the empty list. Proof sketch: use the empty-list rule for filtering. -/
theorem emptyOn_iff_filter_eq_nil (rows : List α) (p : α → Bool) :
    EmptyOn rows p ↔ rows.filter p = [] := by
  simp [EmptyOn, List.filter_eq_nil_iff]

/-- For any input and filters, the filters are disjoint exactly when every row accepted by the
first passes the complement of the second. Proof sketch: accepting the Boolean complement means rejecting the
original filter. -/
theorem disjointOn_iff_impliesOn_complement (rows : List α) (p q : α → Bool) :
    DisjointOn rows p q ↔ ImpliesOn rows p (fun row => !q row) := by
  simp [DisjointOn, ImpliesOn]

/-- For any two inputs, if the second contains exactly the rows of the first that pass a
restriction, selecting and projecting from the second gives the same bag as selecting with
both filters and projecting from the first. For example, the restriction can describe rows
that survive a DELETE. Proof sketch: filtering and mapping preserve permutations, and
successive filters select the conjunction of their predicates. -/
theorem project_after_restrict {xs ys : List α} {survives : α → Bool}
    (effect : ys.Perm (xs.filter survives)) (keep : α → Bool) (project : α → β) :
    ((ys.filter keep).map project).Perm
      ((xs.filter (fun row => survives row && keep row)).map project) := by
  simpa only [List.filter_filter, Bool.and_comm] using (effect.filter keep).map project

/-- A projection preserves the length of both lists, so a sublist with the same projected
bag as the original list contains every entry. -/
private theorem projected_sublist_perm_iff {xs ys : List α} (sub : ys.Sublist xs) (project : α → β) :
    (ys.map project).Perm (xs.map project) ↔ ys = xs := by
  refine ⟨fun same => sub.eq_of_length (by simpa using same.length_eq), ?_⟩
  rintro rfl
  exact List.Perm.refl _

/-- For every input, two filters and a projection, adding the extra filter preserves the
projected bag exactly when every selected input row passes that filter ({name}`ImpliesOn`).
Even a constant projection records one entry per selected row. Proof sketch: filtering
takes a sublist. Its projection has the original bag exactly when the sublist is the full
selected list, which means every selected row passes the extra filter. -/
theorem project_restrict_iff (xs : List α) (keep extra : α → Bool) (project : α → β) :
    ((xs.filter (fun row => extra row && keep row)).map project).Perm ((xs.filter keep).map project) ↔
      ImpliesOn xs keep extra := by
  rw [← List.filter_filter, projected_sublist_perm_iff List.filter_sublist, List.filter_eq_self]
  simp [ImpliesOn, List.mem_filter]

end Belay.Sqlite.Model.RowFilter
