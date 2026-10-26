import Belay.Sqlite.Model.TwoStateNotExistsExcept
import Belay.Sqlite.Model.RowDelete
import Belay.Sqlite.Model.PlainInsertRows
import Belay.Sqlite.Model.ForeignKeyLookupRemoval

set_option doc.verso true

/-! The rows of the two terms of {lit}`SELECT … FROM before.t WHERE p EXCEPT SELECT … FROM t` over a table and the
table that a {lit}`DELETE` leaves (ADR 0017, S6). The first term reads the rows of the table before the delete for
which {lit}`p` is true; the second reads every row of the table after it. When {lit}`p` is true for a row only if
the delete does not select the row, the second term has every row of the first. If the first column is the rowid
alias, the rows of the first term are identical where they compare equal. -/

namespace Belay.Sqlite.Model

/-- For every context, rows, condition and columns, a row is a result of the first term exactly when the output of a
source row that the condition keeps. In plain words: the term outputs the columns of the rows with a true condition.
Proof sketch: the rows of a simple query are the output rows of the rows that {lit}`WHERE` keeps
({name}`Resolved.Query.Simple.results_eq`). -/
theorem Resolved.initialTerm_mem_results (position : Nat) (condition : Resolved.Expr) (columns : List Resolved.Expr)
    (names : List String) (context : Resolved.EvalContext) (rows : List (List Value)) (output : List Value) :
    output ∈ (Resolved.initialTerm position condition columns names).results context rows ↔
      ∃ row ∈ rows, Resolved.truthy (condition.eval context row) = true ∧ output = columns.map (·.eval context row) := by
  rw [(Resolved.Query.simple_isSimple _ _ _ _).results_eq]
  simp only [List.mem_map, Resolved.mem_filtered, Resolved.Query.simple, Option.all_some]
  constructor
  · rintro ⟨row, ⟨member, kept⟩, rfl⟩
    exact ⟨row, member, kept, by simp [Function.comp_def]⟩
  · rintro ⟨row, member, kept, rfl⟩
    exact ⟨row, ⟨member, kept⟩, by simp [Function.comp_def]⟩

/-- For every context, rows and columns, a row is a result of the second term exactly when it is the output of a source
row. In plain words: the term outputs the columns of every row. Proof sketch: as
{name}`Resolved.initialTerm_mem_results`, without a condition. -/
theorem Resolved.currentTerm_mem_results (position : Nat) (columns : List Resolved.Expr) (names : List String)
    (context : Resolved.EvalContext) (rows : List (List Value)) (output : List Value) :
    output ∈ (Resolved.currentTerm position columns names).results context rows ↔
      ∃ row ∈ rows, output = columns.map (·.eval context row) := by
  rw [(Resolved.Query.simple_isSimple _ _ _ _).results_eq]
  simp only [List.mem_map, Resolved.mem_filtered, Resolved.Query.simple, Option.all_none, and_true]
  constructor
  · rintro ⟨row, member, rfl⟩
    exact ⟨row, member, by simp [Function.comp_def]⟩
  · rintro ⟨row, member, rfl⟩
    exact ⟨row, member, by simp [Function.comp_def]⟩

/-- For every table, delete filter and context of the delete, condition and columns of the first term, and context of
the values: when the condition is true for a row only if the filter is not true for it, every result of the first term
over the table is a result of the second term over the table that the delete leaves. In plain words: a row that the
check keeps is a row that the delete keeps. Proof sketch: a result comes from a scanned row with a true condition; the
filter is not true for that row, so {name}`LiteralData.deleted` keeps it, and the second term outputs the same columns
of it. -/
theorem Resolved.notExistsExcept_subset (position : Nat) (condition : Resolved.Expr) (columns : List Resolved.Expr)
    (names : List String) (table : Table) (filter : Resolved.Expr) (deleteContext context : Resolved.EvalContext)
    (complement : ∀ row ∈ table.rows, Resolved.truthy (condition.eval context row.values) = true →
      Resolved.truthy (filter.eval deleteContext row.values) = false) :
    ∀ output ∈ (Resolved.initialTerm position condition columns names).results context (Resolved.sourceRows table),
      output ∈ (Resolved.currentTerm position columns names).results context
        (Resolved.sourceRows (LiteralData.deleted deleteContext table (some filter))) := by
  intro output member
  obtain ⟨cells, scanned, kept, rfl⟩ := (Resolved.initialTerm_mem_results _ _ _ _ _ _ _).1 member
  obtain ⟨row, inTable, rfl⟩ := (mem_sourceRows_iff table cells).1 scanned
  refine (Resolved.currentTerm_mem_results _ _ _ _ _ _).2 ⟨row.values, (mem_sourceRows_iff _ _).2 ⟨row, ?_, rfl⟩, rfl⟩
  simp only [LiteralData.deleted, List.mem_filter, LiteralData.selected, Option.all_some, Bool.not_eq_true']
  exact ⟨inTable, complement row inTable kept⟩

/-- For every table with distinct rowids whose rowid alias is the first column, every context, condition, and columns
and collations that both start with the first column: no two results of the first term over the table compare equal
unless they are the same list. In plain words: equal keys mean the same row. Proof sketch: the first cell of a row
is its rowid ({name}`Row.Aliased`), so two results that compare equal in the first cell come from rows with
the same rowid, which are one row ({name}`Table.RowidsDistinct.row_eq`). -/
theorem Resolved.notExistsExcept_identical (position : Nat) (condition : Resolved.Expr) (first : Resolved.Expr)
    (columns : List Resolved.Expr) (names : List String) (collation : Collation) (collations : List Collation)
    (table : Table) (context : Resolved.EvalContext) (distinct : table.RowidsDistinct) (aliased : table.RowsAliased)
    (alias : table.shape.rowidAlias = some 0) (firstColumn : first = .column 0) :
    Resolved.equalRowsIdentical (collation :: collations)
      ((Resolved.initialTerm position condition (first :: columns) names).results context (Resolved.sourceRows table)) =
      true := by
  unfold Resolved.equalRowsIdentical
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
  intro left leftMember right rightMember
  by_cases same : Resolved.sameOutput (collation :: collations) left right = true
  · right
    obtain ⟨leftCells, leftScanned, -, rfl⟩ := (Resolved.initialTerm_mem_results _ _ _ _ _ _ _).1 leftMember
    obtain ⟨rightCells, rightScanned, -, rfl⟩ := (Resolved.initialTerm_mem_results _ _ _ _ _ _ _).1 rightMember
    obtain ⟨leftRow, leftIn, rfl⟩ := (mem_sourceRows_iff table leftCells).1 leftScanned
    obtain ⟨rightRow, rightIn, rfl⟩ := (mem_sourceRows_iff table rightCells).1 rightScanned
    have leftKey := aliased leftRow leftIn 0 alias
    have rightKey := aliased rightRow rightIn 0 alias
    have compared : collation.compare (leftRow.values.getD 0 .null) (rightRow.values.getD 0 .null) = .eq := by
      unfold Resolved.sameOutput at same
      simp only [Bool.and_eq_true, List.all_eq_true] at same
      have head := same.2 (collation, leftRow.values.getD 0 .null, rightRow.values.getD 0 .null) (by
        simp [firstColumn, Resolved.Expr.eval, Resolved.Expr.evaluate])
      simpa using head
    simp only [List.getD_eq_getElem?_getD, leftKey, rightKey, Option.getD_some,
      Collation.compare_integer, Int.compare_eq_eq] at compared
    have sameRow : leftRow = rightRow := distinct.row_eq leftIn rightIn compared
    rw [sameRow]
  · left
    simpa using same

end Belay.Sqlite.Model
