import Belay.Sqlite.Model.Queries.Evaluation.CorrelatedSubqueryRun

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- For every list and test, the rows kept by the test, mapped to anything, are empty exactly when no element passes
the test. Proof sketch: a list is empty when no element is kept ({name}`List.filter_eq_nil_iff`). -/
theorem isEmpty_filter_map {α β : Type} (elements : List α) (keep : α → Bool) (change : α → β) :
    ((elements.filter keep).map change).isEmpty = !elements.any keep := by
  rw [List.isEmpty_map]
  cases hany : elements.any keep
  · exact List.isEmpty_iff.mpr (List.filter_eq_nil_iff.mpr (by simpa using List.any_eq_false.mp hany))
  · obtain ⟨element, member, kept⟩ := List.any_eq_true.mp hany
    rw [List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem (List.mem_filter.mpr ⟨member, kept⟩))]
    rfl

end Belay.Sqlite.Model.Resolved
