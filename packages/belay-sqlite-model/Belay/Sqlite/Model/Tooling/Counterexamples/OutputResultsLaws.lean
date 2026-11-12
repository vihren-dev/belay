import Belay.Sqlite.Model.Programs.Claims.OutputResultsLaws

set_option doc.verso true

/-! What the output of a query says about the results that SQLite may give for it
({name}`Belay.Sqlite.Model.Output.ofResults`): the output has rows exactly when there is at least one
result and each result has a row, has no rows exactly when there is at least one result and each
result is empty, and is never an error (ADR 0017, S4). -/

namespace Belay.Sqlite.Model

/-- For every list of results and every property of a result, lists with the same members agree
that there is a member and that each member has the property: the claim for {lit}`rs` is the claim
for {lit}`listed`. Proof sketch: the members are the same, so the two claims are the same. -/
theorem Output.listed_iff (rs listed : List (List (List Value))) (mem : ∀ x, x ∈ listed ↔ x ∈ rs)
    (property : List (List Value) → Prop) :
    (rs ≠ [] ∧ ∀ result ∈ rs, property result) ↔ (listed ≠ [] ∧ ∀ result ∈ listed, property result) := by
  have same : listed = [] ↔ rs = [] := by
    simp only [List.eq_nil_iff_forall_not_mem, mem]
  exact and_congr (not_congr same.symm) ⟨fun h r m => h r ((mem r).1 m), fun h r m => h r ((mem r).2 m)⟩

/-- For every list of results {lit}`rs`, {name}`Output.ofResults` of it has rows
({name}`Output.hasRows`) exactly when {lit}`rs` is not empty and no result in it is empty. With no
result, the output is {name}`Output.unmodeled`, which has no rows. Proof sketch: the output lists
the same results ({name}`Output.ofResults_listed`); one case for each shape of the list. -/
theorem Output.hasRows_ofResults (rs : List (List (List Value))) :
    (Output.ofResults rs).hasRows = true ↔ rs ≠ [] ∧ ∀ result ∈ rs, result ≠ [] := by
  obtain ⟨listed, mem, eq⟩ := Output.ofResults_listed rs
  rw [eq, Output.listed_iff rs listed mem]
  match listed with
  | [] => simp [Output.hasRows]
  | [result] => simp [Output.hasRows]
  | first :: second :: rest => simp [Output.hasRows]

/-- For every list of results {lit}`rs`, {name}`Output.ofResults` of it has no rows
({name}`Output.hasNoRows`) exactly when {lit}`rs` is not empty and every result in it is empty.
Proof sketch: as {name}`Output.hasRows_ofResults`. -/
theorem Output.hasNoRows_ofResults (rs : List (List (List Value))) :
    (Output.ofResults rs).hasNoRows = true ↔ rs ≠ [] ∧ ∀ result ∈ rs, result = [] := by
  obtain ⟨listed, mem, eq⟩ := Output.ofResults_listed rs
  rw [eq, Output.listed_iff rs listed mem]
  match listed with
  | [] => simp [Output.hasNoRows]
  | [result] => simp [Output.hasNoRows]
  | first :: second :: rest => simp [Output.hasNoRows]

/-- For every list of results {lit}`rs` and every property {lit}`Q` of a result:
{name}`Output.ofResults` of {lit}`rs` returns a result with {lit}`Q`
({name}`Output.returnsResult`) exactly when {lit}`rs` is not empty and each result in it
satisfies {lit}`Q`. With no result, the output is {name}`Output.unmodeled`, which returns
nothing. Proof sketch: the output lists the same results ({name}`Output.ofResults_listed`);
one case for each shape of the list. -/
theorem Output.returnsResult_ofResults (rs : List (List (List Value))) (property : List (List Value) → Prop) :
    (Output.ofResults rs).returnsResult property ↔ rs ≠ [] ∧ ∀ result ∈ rs, property result := by
  obtain ⟨listed, mem, eq⟩ := Output.ofResults_listed rs
  rw [eq, Output.listed_iff rs listed mem]
  match listed with
  | [] => simp [Output.returnsResult]
  | [result] => simp [Output.returnsResult]
  | first :: second :: rest => simp [Output.returnsResult]

end Belay.Sqlite.Model
