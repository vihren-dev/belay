import Belay.Sqlite.Model.InSubqueryFilterLaw

set_option doc.verso true

/-! The usual syntactic forms of the correlated condition of the filter laws (task 20261027): the comparison
{lit}`u.e = x` alone, and the comparison after a guard {lit}`w`, which is the {lit}`WHERE` of the {lit}`IN` subquery. The
joined rows of a subquery start with the outer cells, so a column of the outer row has the same value in every joined
row. -/

namespace Belay.Sqlite.Model.Resolved

/-- If the second operand {lit}`probe` has the probe value in every joined row, the correlated condition
{lit}`e = probe` of the subquery keeps a joined row exactly when the {lit}`IN` subquery without a condition would keep it
and {lit}`e` equals the probe value. In symbols: {name}`CorrelatedEquality` for no condition of the {lit}`IN` subquery and
the condition {lit}`Expr.compare .eq` of the result expression and the probe expression. Proof sketch: the evaluation of
the comparison is {name}`equalsValue` of the operands. -/
theorem correlatedEquality_of_compare (inner : EvalContext) (affinity : Option Affinity) (collation : Collation)
    (projection probeInner : Expr) (value : Value) (rows : List (List Value))
    (sameProbe : ∀ row ∈ rows, probeInner.eval inner row = value) :
    CorrelatedEquality inner affinity collation none (some (.compare .eq affinity projection probeInner collation))
      projection value rows := by
  intro row member
  have probe := sameProbe row member
  subst probe
  rfl

/-- The same with a guard: the {lit}`IN` subquery has the condition {lit}`w`, and the correlated condition is
{lit}`w AND e = probe`. Proof sketch: the truth of {lit}`AND` is the conjunction of the truths
({name}`truthy_and`); the rest is {name}`correlatedEquality_of_compare`. -/
theorem correlatedEquality_of_guarded_compare (inner : EvalContext) (affinity : Option Affinity)
    (collation : Collation) (guard projection probeInner : Expr) (value : Value) (rows : List (List Value))
    (sameProbe : ∀ row ∈ rows, probeInner.eval inner row = value) :
    CorrelatedEquality inner affinity collation (some guard)
      (some (.and guard (.compare .eq affinity projection probeInner collation))) projection value rows := by
  intro row member
  have probe := sameProbe row member
  subst probe
  simp only [conditionKeeps, Option.all_some, Expr.eval_and, truthy_and]
  rfl

/-- For every joined row of a subquery, the cell at a position inside the width {lit}`outer` is the cell of the outer
row. Proof sketch: the joined row starts with the outer cells ({name}`outerCells_getD`). -/
theorem joinedRows_getD_outer {outer : Nat} {outerRow row : List Value} {table : Table} {key : Nat}
    (member : row ∈ joinedRows outer outerRow table) (inside : key < outer) :
    row.getD key .null = outerRow.getD key .null := by
  obtain ⟨cells, _, rfl⟩ := List.mem_map.mp member
  rw [getD_append_of_lt _ _ (by rw [outerCells_length]; exact inside), outerCells_getD outer outerRow inside]

/-- For every joined row of a subquery and every column, there is a row of the table whose cell at the column is the
cell of the joined row at the position {lit}`outer + column`. Proof sketch: the joined row is the outer cells, which
have {lit}`outer` cells ({name}`outerCells_length`), followed by the cells of a table row. -/
theorem joinedRows_getD_cell {outer : Nat} {outerRow row : List Value} {table : Table}
    (member : row ∈ joinedRows outer outerRow table) (column : Nat) :
    ∃ cells ∈ sourceRows table, row.getD (outer + column) .null = cells.getD column .null := by
  obtain ⟨cells, inRows, rfl⟩ := List.mem_map.mp member
  refine ⟨cells, inRows, ?_⟩
  have := getD_append_length_add (outerCells outer outerRow) cells column .null
  rwa [outerCells_length] at this

end Belay.Sqlite.Model.Resolved
