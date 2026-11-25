import Belay

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the claim-proof pilot, form B, deletes the laws of
the form `SELECT 1 WHERE NOT EXISTS (SELECT … FROM before.t WHERE p EXCEPT SELECT … FROM t)` and the truth law of
`(a AND b) IS NOT 1`. This module and `PurgeLawRetentionOutput` prove their statements from the laws that remain, so
the deletion loses no capability. The statements are copied from the revision of the base form, and the definitions
of the form that they need are restated here. -/

set_option doc.verso true

namespace PurgeLawRetention
open Belay.Sqlite.Model

/-- The first term of the compound: the columns and the condition over the table at a position of the initial
database, in written order. -/
abbrev Resolved.initialTerm (position : Nat) (condition : Resolved.Expr) (columns : List Resolved.Expr)
    (names : List String) : Resolved.Query :=
  Resolved.Query.simple [{ kind := .inner, source := .initialTable position, condition := none }] (some condition)
    (columns.map Resolved.Output.scalar) names

/-- The second term of the compound: the columns of the table at a position of the current database, without
a condition. -/
abbrev Resolved.currentTerm (position : Nat) (columns : List Resolved.Expr) (names : List String) : Resolved.Query :=
  Resolved.Query.simple [Resolved.QuerySource.first position] none (columns.map Resolved.Output.scalar) names

/-- For every sources, optional filter, columns, names, context and rows: the one result of the simple query is the
values of the columns over each row for which the filter is true, in the order of the rows. Proof sketch: the
results of a plain query without ordering are the outputs of the rows that {lit}`WHERE` keeps
({name}`Resolved.Query.results_plain_unordered`). -/
theorem simple_results (sources : List Resolved.QuerySource) (filter : Option Resolved.Expr)
    (columns : List Resolved.Expr) (names : List String) (context : Resolved.EvalContext) (rows : List (List Value)) :
    (Resolved.Query.simple sources filter (columns.map .scalar) names).results context rows =
      (rows.filter fun row => filter.all fun condition => Resolved.truthy (condition.eval context row)).map
        fun row => columns.map (·.eval context row) := by
  rw [Resolved.Query.results_plain_unordered context rfl rfl rfl rfl rfl rfl]
  simp [Resolved.filtered, Resolved.Query.rowOutput, Resolved.Query.simple, Function.comp_def]

section
open Belay.Sqlite.Model.Resolved

/-- For every two conditions, context and row: if {lit}`(left AND right) IS NOT 1` is true for the row, then
{lit}`left AND right` is not true for it. The statement of the base form. Proof sketch: {lit}`AND` gives NULL, 0 or 1
({name}`Resolved.Expr.isLogical`), so {name}`Resolved.Expr.truthy_isNot_one` applies. -/
theorem Resolved.Expr.truthy_isNot_one_and (left right : Expr) (context : EvalContext) (row : List Value) :
    truthy ((Expr.compare .isNot none (.and left right) (.literal (.integer 1))).eval context row) = true →
      truthy ((Expr.and left right).eval context row) = false := by
  rw [Expr.truthy_isNot_one (expression := .and left right) rfl]
  simp

end

/-- For every table, delete filter and context of the delete, condition and columns of the first term, and context of
the values: when the condition is true for a row only if the filter is not true for it, every result of the first term
over the table is a result of the second term over the table that the delete leaves. The statement of the base form.
Proof sketch: the results of the terms are filters of the source rows ({name}`simple_results`); a source row is a row
of the table ({name}`mem_sourceRows_iff`), and the delete keeps it ({name}`LiteralData.mem_deleted`). -/
theorem Resolved.notExistsExcept_subset (position : Nat) (condition : Resolved.Expr) (columns : List Resolved.Expr)
    (names : List String) (table : Table) (filter : Resolved.Expr) (deleteContext context : Resolved.EvalContext)
    (complement : ∀ row ∈ table.rows, Resolved.truthy (condition.eval context row.values) = true →
      Resolved.truthy (filter.eval deleteContext row.values) = false) :
    ∀ output ∈ (Resolved.initialTerm position condition columns names).results context (Resolved.sourceRows table),
      output ∈ (Resolved.currentTerm position columns names).results context
        (Resolved.sourceRows (LiteralData.deleted deleteContext table (some filter))) := by
  intro output member
  rw [simple_results] at member ⊢
  simp only [List.mem_map, List.mem_filter, Option.all_some, Option.all_none, and_true] at member ⊢
  obtain ⟨cells, ⟨scanned, kept⟩, rfl⟩ := member
  obtain ⟨row, inTable, rfl⟩ := (mem_sourceRows_iff table cells).1 scanned
  refine ⟨row.values, (mem_sourceRows_iff _ _).2 ⟨row, ?_, rfl⟩, rfl⟩
  rw [LiteralData.mem_deleted]
  simpa [LiteralData.selected] using And.intro inTable (complement row inTable kept)

/-- For every table whose rowids are distinct, whose rowid alias is column 0 and whose rows each store their rowid in
that column, every context, condition, columns whose first column is column 0, and collations with an arbitrary first
collation: no two results of the first term over the table compare equal unless they are the same list. The statement
of the base form. Proof sketch: the results are the outputs of source
rows of the table ({name}`simple_results`), which start with the rowid alias, so
{name}`Resolved.equalRowsIdentical_rowidFirst` applies. -/
theorem Resolved.notExistsExcept_identical (position : Nat) (condition : Resolved.Expr) (first : Resolved.Expr)
    (columns : List Resolved.Expr) (names : List String) (collation : Collation) (collations : List Collation)
    (table : Table) (context : Resolved.EvalContext) (distinct : table.RowidsDistinct) (aliased : table.RowsAliased)
    (alias : table.shape.rowidAlias = some 0) (firstColumn : first = .column 0) :
    Resolved.equalRowsIdentical (collation :: collations)
      ((Resolved.initialTerm position condition (first :: columns) names).results context (Resolved.sourceRows table)) =
      true := by
  subst firstColumn
  rw [simple_results]
  exact Resolved.equalRowsIdentical_rowidFirst distinct aliased alias collation collations context columns
    fun cells member => (List.mem_filter.1 member).1

#print axioms Resolved.Expr.truthy_isNot_one_and
#print axioms Resolved.notExistsExcept_subset
#print axioms Resolved.notExistsExcept_identical

end PurgeLawRetention
