import Belay.Sqlite.QueryLaws

set_option doc.verso true

/-! Laws of joined sources (ADR 0012, amendment 2, "Proofs"): a query without joins reads
the rows of its one table, every joined row has the width of its tables together, and a
left join keeps every left row. -/

namespace Belay.Sqlite.Resolved

/-- For every query without joins and every database, the source rows of the query are
the rows of its table in rowid order ({name}`sourceRows`), or none when the table is
missing: the query of one table is the special case of a join. -/
theorem Query.source_single (query : Query) (database : Database) (single : query.joins = []) :
    query.source database = (database query.table).map sourceRows := by
  unfold Query.source
  rw [single]
  cases database query.table <;> rfl

/-- For every valid table, every row of {name}`sourceRows` has one cell per column.
Proof sketch: the sorted rows are a permutation of the table's rows
({name}`stableSort_perm`), each of which has one cell per column. -/
theorem sourceRows_width {table : Table} (valid : table.Valid) :
    ∀ cells ∈ sourceRows table, cells.length = table.shape.columns.length := by
  intro cells member
  obtain ⟨row, sorted, rfl⟩ := List.mem_map.mp member
  exact (valid.2 row ((stableSort_perm _ _).mem_iff.mp sorted)).2.1

/-- For every width, left row of that width, join and valid table, every row of
{name}`joinMatches` has the width plus one cell per column of the table. -/
theorem joinMatches_width {width : Nat} {row : List Value} {table : Table} (join : Join) (valid : table.Valid)
    (rowWidth : row.length = width) :
    ∀ joined ∈ joinMatches row join table, joined.length = width + table.shape.columns.length := by
  intro joined member
  obtain ⟨cells, cellsMember, built⟩ := List.mem_filterMap.mp member
  dsimp only at built
  split at built <;> cases built
  simp [rowWidth, sourceRows_width valid cells cellsMember]

/-- For every width, left rows of that width, join and valid table, every row of
{name}`joinRows` has the width plus one cell per column of the table: a joined row is a
left row followed by a row of the table, or by NULL padding of that width. Proof sketch:
each row comes from {name}`joinRow` of a left row; a match has the width by
{name}`joinMatches_width`, and the padding has one NULL per column. -/
theorem joinRows_width {width : Nat} {left : List (List Value)} {table : Table} (join : Join)
    (valid : table.Valid) (widths : ∀ row ∈ left, row.length = width) :
    ∀ row ∈ joinRows left join table, row.length = width + table.shape.columns.length := by
  intro row member
  obtain ⟨leftRow, leftMember, joined⟩ := List.mem_flatMap.mp member
  have matched := joinMatches_width join valid (widths leftRow leftMember)
  unfold joinRow at joined
  cases kind : join.kind with
  | inner => simp only [kind] at joined; exact matched row joined
  | left =>
    simp only [kind] at joined
    by_cases empty : (joinMatches leftRow join table).isEmpty
    · simp only [empty, ite_true, List.mem_singleton] at joined
      subst joined
      simp [widths leftRow leftMember]
    · simp only [empty, Bool.false_eq_true, ite_false] at joined
      exact matched row joined

/-- For every left join, left rows and table, every left row is a prefix of some row of
{name}`joinRows`: a left join drops no left row. Proof sketch: a left row with matches is
the prefix of its first match; otherwise it is the prefix of its padded row. -/
theorem joinRows_left_keeps {left : List (List Value)} {table : Table} (join : Join) (kind : join.kind = .left) :
    ∀ leftRow ∈ left, ∃ row ∈ joinRows left join table, leftRow <+: row := by
  intro leftRow member
  have joined : ∀ row ∈ joinRow join table leftRow, row ∈ joinRows left join table :=
    fun row inner => List.mem_flatMap.mpr ⟨leftRow, member, inner⟩
  by_cases empty : (joinMatches leftRow join table).isEmpty
  · refine ⟨leftRow ++ List.replicate table.shape.columns.length .null, joined _ ?_, List.prefix_append _ _⟩
    simp [joinRow, kind, empty]
  · obtain ⟨row, rowMember⟩ := List.exists_mem_of_ne_nil (joinMatches leftRow join table) (by simpa using empty)
    obtain ⟨cells, _, built⟩ := List.mem_filterMap.mp rowMember
    dsimp only at built
    split at built <;> cases built
    refine ⟨leftRow ++ cells, joined _ ?_, List.prefix_append _ _⟩
    simp only [joinRow, kind, empty, Bool.false_eq_true, ite_false]
    exact rowMember

end Belay.Sqlite.Resolved
