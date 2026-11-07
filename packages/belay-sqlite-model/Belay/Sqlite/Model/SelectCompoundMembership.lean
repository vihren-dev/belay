import Belay.Sqlite.Model.SelectDistinctRules

set_option doc.verso true

/-! Membership rules of the compound operators (ADR 0027, D1, phase {lit}`compound`):
{lit}`UNION`, {lit}`INTERSECT` and {lit}`EXCEPT` keep the first row of each set of equal rows
({lit}`distinctRows`), so no two of their rows compare equal. When the equal rows that an operator
reads are the same values ({lit}`equalRowsIdentical`), which the model requires for a certain
compound, membership in the result is membership in the operands: {lit}`UNION` keeps each row of
either operand, {lit}`INTERSECT` each left row that equals a right row, and {lit}`EXCEPT` each left
row that equals no right row. {lit}`UNION ALL` keeps every row with its multiplicity. -/

namespace Belay.Sqlite.Model.Resolved

/-- Distinct-rows rule: for every collations and rows, the first row of each set of equal rows
({name}`distinctRows`):
- is a sublist of the rows;
- has, for each row, a kept row that compares equal to it ({name}`sameOutput`);
- has no two rows that compare equal.
Proof sketch: {name}`distinctRows` is the fold of {name}`keepFirst` with the rows as keys
({name}`keepFirst_fold`), and a row compares equal to itself ({name}`sameOutput_self`). -/
theorem distinctRows_rules (collations : List Collation) (rows : List (List Value)) :
    (distinctRows collations rows).Sublist rows ∧
      (∀ row ∈ rows, ∃ kept ∈ distinctRows collations rows, sameOutput collations kept row = true) ∧
      (distinctRows collations rows).Pairwise (fun earlier later => sameOutput collations earlier later = false) := by
  have fold : distinctRows collations rows = rows.foldl (keepFirst (sameOutput collations) id) [] := rfl
  obtain ⟨sublist, -, covers, pairwise⟩ := keepFirst_fold (sameOutput collations) id rows []
  rw [fold]
  refine ⟨by simpa using sublist, fun row member => ?_, pairwise .nil⟩
  obtain ⟨kept, keptMember, same⟩ := covers row member
  rcases same with rfl | same
  · exact ⟨kept, keptMember, sameOutput_self collations kept⟩
  · exact ⟨kept, keptMember, same⟩

/-- For every collations and rows whose equal rows are the same values
({name}`equalRowsIdentical`), two of the rows that compare equal ({name}`sameOutput`) are the same
row. -/
theorem eq_of_equalRowsIdentical {collations : List Collation} {rows : List (List Value)}
    (identical : equalRowsIdentical collations rows = true) {first second : List Value} (firstMember : first ∈ rows)
    (secondMember : second ∈ rows) (same : sameOutput collations first second = true) : first = second := by
  unfold equalRowsIdentical at identical
  have pair := List.all_eq_true.mp (List.all_eq_true.mp identical first firstMember) second secondMember
  simpa [same] using pair

/-- For every collations, rows whose equal rows are the same values ({name}`equalRowsIdentical`)
and row, the row is a row of {name}`distinctRows` exactly when it is one of the rows. Proof sketch:
the kept row that compares equal to a row ({name}`distinctRows_rules`) is the row. -/
theorem mem_distinctRows_iff {collations : List Collation} {rows : List (List Value)}
    (identical : equalRowsIdentical collations rows = true) (row : List Value) :
    row ∈ distinctRows collations rows ↔ row ∈ rows := by
  obtain ⟨sublist, covers, -⟩ := distinctRows_rules collations rows
  refine ⟨fun member => sublist.subset member, fun member => ?_⟩
  obtain ⟨kept, keptMember, same⟩ := covers row member
  exact eq_of_equalRowsIdentical identical (sublist.subset keptMember) member same ▸ keptMember

/-- For every collations and operator other than {lit}`UNION ALL`, and left and right rows, no
two rows of the operator's result ({name}`CompoundOperator.combine`) compare equal
({name}`sameOutput`). Proof sketch: each such result is {name}`distinctRows` or a filter of it
({name}`distinctRows_rules`). -/
theorem combine_pairwise (collations : List Collation) {operator : CompoundOperator}
    (notAll : operator ≠ .unionAll) (left right : List (List Value)) :
    (operator.combine collations left right).Pairwise fun earlier later => sameOutput collations earlier later = false := by
  cases operator with
  | unionAll => exact absurd rfl notAll
  | union => exact (distinctRows_rules collations _).2.2
  | intersect | except => exact (distinctRows_rules collations left).2.2.filter _

/-- {lit}`UNION` rule: for every collations, left and right rows whose equal rows together are the
same values ({name}`equalRowsIdentical`) and row, the row is in the result of {lit}`UNION` exactly
when it is a left row or a right row. Proof sketch: {name}`mem_distinctRows_iff`. -/
theorem mem_union_combine {collations : List Collation} {left right : List (List Value)}
    (identical : equalRowsIdentical collations (left ++ right) = true) (row : List Value) :
    row ∈ CompoundOperator.union.combine collations left right ↔ row ∈ left ∨ row ∈ right := by
  simp [CompoundOperator.combine, mem_distinctRows_iff identical]

/-- {lit}`INTERSECT` rule: for every collations, left rows whose equal rows are the same values
({name}`equalRowsIdentical`), right rows and row, the row is in the result of {lit}`INTERSECT`
exactly when it is a left row that compares equal to some right row ({name}`sameOutput`). Proof
sketch: a filter of {name}`distinctRows` and {name}`mem_distinctRows_iff`. -/
theorem mem_intersect_combine {collations : List Collation} {left : List (List Value)}
    (identical : equalRowsIdentical collations left = true) (right : List (List Value)) (row : List Value) :
    row ∈ CompoundOperator.intersect.combine collations left right ↔
      row ∈ left ∧ right.any (sameOutput collations row) = true := by
  simp [CompoundOperator.combine, mem_distinctRows_iff identical]

/-- {lit}`EXCEPT` rule: for every collations, left rows whose equal rows are the same values
({name}`equalRowsIdentical`), right rows and row, the row is in the result of {lit}`EXCEPT`
exactly when it is a left row that compares equal to no right row ({name}`sameOutput`). Proof
sketch: a filter of {name}`distinctRows` and {name}`mem_distinctRows_iff`. -/
theorem mem_except_combine {collations : List Collation} {left : List (List Value)}
    (identical : equalRowsIdentical collations left = true) (right : List (List Value)) (row : List Value) :
    row ∈ CompoundOperator.except.combine collations left right ↔
      row ∈ left ∧ right.any (sameOutput collations row) = false := by
  simp [CompoundOperator.combine, mem_distinctRows_iff identical]

/-- For every collations and rows of which no two compare equal ({name}`sameOutput`), the rows
have no duplicate. Proof sketch: a row compares equal to itself ({name}`sameOutput_self`). -/
theorem nodup_of_pairwise_sameOutput {collations : List Collation} {rows : List (List Value)}
    (unique : rows.Pairwise fun earlier later => sameOutput collations earlier later = false) : rows.Nodup :=
  unique.imp fun different equal => by
    subst equal
    simp [sameOutput_self] at different

end Belay.Sqlite.Model.Resolved
