import Belay.Sqlite.QueryLaws
import Belay.Sqlite.QueryFunctions

set_option doc.verso true

/-! Laws of joined sources (ADR 0012, amendments 2 and 3, "Proofs"; ADR 0013, D5): a query
of one table reads the rows of its table and a query without sources one row with no
cells, every joined row has the width of its sources together, a left or full join keeps
every left row, and a right or full join keeps every row of its source. -/

namespace Belay.Sqlite.Resolved

/-- For every context value, query whose only source is a table, as an inner join without a
condition, and every database, the source rows of the query in the context are the rows of its table in rowid order
({name}`sourceRows`), or none when the table is missing: the query of one table is the
special case of a join. -/
theorem Query.source_single (context : EvalContext) (query : Query) (database : Database) (table : Nat)
    (single : query.sources = [{ kind := .inner, source := .table table, condition := none }]) :
    (query.source context database).map (·.rows) = (database.table table).map sourceRows := by
  simp only [Query.source, single, List.foldlM, QuerySource.join]
  cases database.table table with
  | none => rfl
  | some found =>
    simp [joinRows, joinRow, joinMatches, QuerySource.matches, bind, Option.bind, pure]

/-- For every context value, query without sources ({lit}`SELECT` without {lit}`FROM`) and
every database, the source is one row with no cells, without a fault. -/
theorem Query.source_none (context : EvalContext) (query : Query) (database : Database) (none_ : query.sources = []) :
    query.source context database = some { rows := [[]], width := 0, fault := .none } := by
  simp only [Query.source, none_, List.foldlM]
  rfl

/-- For every valid table, every row of {name}`sourceRows` has one cell per column.
Proof sketch: the scanned rows are a permutation of the table's rows
({name}`Belay.Sqlite.Table.scanRows_perm`), each of which has one cell per column. -/
theorem sourceRows_width {table : Table} (valid : table.Valid) :
    ∀ cells ∈ sourceRows table, cells.length = table.shape.columns.length := by
  intro cells member
  obtain ⟨row, sorted, rfl⟩ := List.mem_map.mp member
  exact (valid.2 row (table.scanRows_perm.mem_iff.mp sorted)).2.1

/-- For every context value, width, left row of that width, join, and candidate rows of
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

/-- For every context value, width, left row of that width, join, and candidate rows of
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

/-- For every context value, width, left rows of that width, join, and candidate rows of
{lit}`columns` cells each, every row of {name}`joinRows` in the context has the width plus {lit}`columns` cells: a joined
row is a left row followed by a candidate or by NULL padding, or, for a right or full join,
NULL padding of the width followed by a candidate. Proof sketch: a row of the first part has
the width by {name}`joinRow_width`; an added right row is a candidate after the width's
NULLs. Use {name}`sourceRows_width` for the rows of a valid table. -/
theorem joinRows_width (context : EvalContext) {width : Nat} {left : List (List Value)} {candidates : List (List Value)} {columns : Nat} (join : QuerySource)
    (valid : ∀ cells ∈ candidates, cells.length = columns) (widths : ∀ row ∈ left, row.length = width) :
    ∀ row ∈ joinRows context width left join columns candidates, row.length = width + columns := by
  intro row member
  unfold joinRows at member
  rcases List.mem_append.mp member with joined | added
  · obtain ⟨leftRow, leftMember, joined⟩ := List.mem_flatMap.mp joined
    exact joinRow_width context join valid (widths leftRow leftMember) row joined
  · cases kind : join.kind <;> simp only [kind, List.not_mem_nil] at added
    all_goals
      obtain ⟨cells, unmatched, rfl⟩ := List.mem_map.mp added
      simp [valid cells (List.mem_filter.mp unmatched).1]

/-- For every context value, left or full join, width, left rows and candidate rows, every
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

/-- For every context value, right or full join, width, left rows and candidate rows, every
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

end Belay.Sqlite.Resolved
