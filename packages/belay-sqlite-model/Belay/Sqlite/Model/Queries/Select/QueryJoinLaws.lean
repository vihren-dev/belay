import Belay.Sqlite.Model.Queries.Evaluation.QueryLaws
import Belay.Sqlite.Model.Queries.Evaluation.QueryFunctions

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- For every evaluation context, width, left row of that width, join, and candidate rows of
{lit}`columns` cells each, every row of {name}`joinMatches` in the context has the width plus {lit}`columns` cells. Proof
sketch: a match is the left row followed by a candidate. -/
theorem joinMatches_width (context : EvalContext) {width : Nat} {row : List Value} {candidates : List (List Value)} {columns : Nat} (join : QuerySource) (valid : ∀ cells ∈ candidates, cells.length = columns)
    (rowWidth : row.length = width) :
    ∀ joined ∈ joinMatches context row join candidates, joined.length = width + columns := by
  intro joined member
  obtain ⟨cells, cellsMember, built⟩ := List.mem_filterMap.mp member
  dsimp only at built
  split at built <;> cases built
  simp [rowWidth, valid cells cellsMember]

/-- For every evaluation context, width, left row of that width, join, and candidate rows of
{lit}`columns` cells each, every row of {name}`joinRow` in the context has the width plus {lit}`columns` cells: a match by
{name}`joinMatches_width`, or the left row padded with one NULL per column. -/
theorem joinRow_width (context : EvalContext) {width : Nat} {leftRow : List Value} {candidates : List (List Value)} {columns : Nat} (join : QuerySource) (valid : ∀ cells ∈ candidates, cells.length = columns)
    (rowWidth : leftRow.length = width) :
    ∀ row ∈ joinRow context join columns candidates leftRow, row.length = width + columns := by
  intro row joined
  have matched := joinMatches_width context join valid rowWidth
  unfold joinRow at joined
  cases kind : join.kind <;> simp only [kind] at joined
  · exact matched row joined
  all_goals first
    | exact matched row joined
    | by_cases empty : (joinMatches context leftRow join candidates).isEmpty
      · simp only [empty, ite_true, List.mem_singleton] at joined
        subst joined
        simp [rowWidth]
      · simp only [empty, Bool.false_eq_true, ite_false] at joined
        exact matched row joined

/-- For every evaluation context, left or full join, width, left rows and candidate rows, every
left row is a prefix of some row of {name}`joinRows` in the context: such a join drops no left row. Proof sketch: a left row with
matches is the prefix of its first match; otherwise it is the prefix of its padded row. -/
theorem joinRows_left_keeps (context : EvalContext) {width : Nat} {left : List (List Value)} {candidates : List (List Value)} {columns : Nat} (join : QuerySource)
    (kind : join.kind = .left ∨ join.kind = .full) :
    ∀ leftRow ∈ left, ∃ row ∈ joinRows context width left join columns candidates, leftRow <+: row := by
  intro leftRow member
  have joined : ∀ row ∈ joinRow context join columns candidates leftRow, row ∈ joinRows context width left join columns candidates :=
    fun row inner => List.mem_append_left _ (List.mem_flatMap.mpr ⟨leftRow, member, inner⟩)
  have padded : joinRow context join columns candidates leftRow = if (joinMatches context leftRow join candidates).isEmpty
      then [leftRow ++ List.replicate columns .null] else joinMatches context leftRow join candidates := by
    rcases kind with kind | kind <;> simp [joinRow, kind]
  by_cases empty : (joinMatches context leftRow join candidates).isEmpty
  · refine ⟨leftRow ++ List.replicate columns .null, joined _ ?_, List.prefix_append _ _⟩
    simp [padded, empty]
  · obtain ⟨row, rowMember⟩ := List.exists_mem_of_ne_nil (joinMatches context leftRow join candidates) (by simpa using empty)
    obtain ⟨cells, _, built⟩ := List.mem_filterMap.mp rowMember
    dsimp only at built
    split at built <;> cases built
    refine ⟨leftRow ++ cells, joined _ ?_, List.prefix_append _ _⟩
    simp only [padded, empty, Bool.false_eq_true, ite_false]
    exact rowMember

/-- For every evaluation context, right or full join, width, left rows and candidate rows, every
candidate is a suffix of some row of {name}`joinRows` in the context: such a join drops no row of its source. Proof sketch: a
row that some left row matches ends that left row's match; a row that no left row matches
is in {name}`unmatchedRight` and ends its padded row. -/
theorem joinRows_right_keeps (context : EvalContext) {width : Nat} {left : List (List Value)} {candidates : List (List Value)} {columns : Nat} (join : QuerySource)
    (kind : join.kind = .right ∨ join.kind = .full) :
    ∀ cells ∈ candidates, ∃ row ∈ joinRows context width left join columns candidates, cells <:+ row := by
  intro cells member
  by_cases found : left.any fun row => join.matches context (row ++ cells)
  · obtain ⟨leftRow, leftMember, matched⟩ := List.any_eq_true.mp found
    have isMatch : leftRow ++ cells ∈ joinMatches context leftRow join candidates :=
      List.mem_filterMap.mpr ⟨cells, member, by simp [matched]⟩
    have inRow : leftRow ++ cells ∈ joinRow context join columns candidates leftRow := by
      have nonempty : (joinMatches context leftRow join candidates).isEmpty = false :=
        List.isEmpty_eq_false_iff_exists_mem.mpr ⟨_, isMatch⟩
      rcases kind with kind | kind <;> simp only [joinRow, kind, nonempty, Bool.false_eq_true, ite_false] <;>
        exact isMatch
    exact ⟨leftRow ++ cells, List.mem_append_left _ (List.mem_flatMap.mpr ⟨leftRow, leftMember, inRow⟩),
      List.suffix_append _ _⟩
  · have unmatched : cells ∈ unmatchedRight context left join candidates := List.mem_filter.mpr ⟨member, by simpa using found⟩
    refine ⟨List.replicate width .null ++ cells, ?_, List.suffix_append _ _⟩
    unfold joinRows
    rcases kind with kind | kind <;> simp only [kind] <;>
      exact List.mem_append_right _ (List.mem_map.mpr ⟨cells, unmatched, rfl⟩)

end Belay.Sqlite.Model.Resolved
