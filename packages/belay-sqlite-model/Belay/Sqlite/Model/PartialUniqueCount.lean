import Belay.Sqlite.Model

set_option doc.verso true

/-!
The bound of a unique lookup in a partial index (ADR 0017, S6). In a table whose keys are unique,
a partial unique index on a column with the filter {lit}`p` allows at most one row for which
{lit}`p` is true and the column equals a given value. The bound of
{lit}`Table.KeysUnique.countMatching_le_one` covers keys without a filter.
-/

namespace Belay.Sqlite.Model

/-- For every table, key with a filter and one column term, and condition: if the table satisfies
{name}`Table.KeysUnique` for the keys and {name}`Table.RowsStored`, the key is one of the keys, the condition
implies the filter of the key (as the key reads it, with the plain context), and the comparison
{lit}`cell = value` has the affinity of the column and the collation of the key term, with a right operand that
depends on no row, then at most one stored row makes {lit}`guard AND cell = value` true, so
{name}`Resolved.countMatching` of the conjunction is at most one. A row for which the guard is false is not counted,
but it may still be in the index and subject to it. Proof sketch: two rows that make the conjunction true are in the index
({lit}`restricts`) and conflict on the key ({name}`Resolved.keyCellsEqual_of_accepted`), which the table forbids
for rows in the list ({name}`filter_length_le_one_of_pairwise`). -/
theorem Table.KeysUnique.countMatching_partial_le_one {keys : List UniqueKey} {table : Table}
    (unique : table.KeysUnique keys) (stored : table.RowsStored) {key : UniqueKey} (member : key ∈ keys)
    {index : Nat} {descending : Bool} {collation : Collation} {column : CatalogColumn}
    (columnAt : table.shape.columns[index]? = some column) {filter : Resolved.Expr}
    (filtered : key.filter = some filter)
    (oneTerm : key.terms = [{ term := .column index, descending, collation }])
    (context : Resolved.EvalContext) (guard value : Resolved.Expr) (cell : Value)
    (restricts : ∀ row : List Value, Resolved.truthy (guard.eval context row) = true →
      Resolved.truthy (filter.eval (.plain 0) row) = true)
    (constant : ∀ row : List Value, value.eval context row = cell) :
    Resolved.countMatching context
      (some (.and guard (.compare .eq (some column.affinity) (.column index) value collation))) table ≤ 1 := by
  rw [Resolved.countMatching_eq]
  refine filter_length_le_one_of_pairwise ((unique key member).imp_of_mem fun {first second} firstMember secondMember distinct both => ?_)
  simp only [Option.all_some, Resolved.Expr.eval_and, Resolved.truthy_and, Bool.and_eq_true] at both
  obtain ⟨⟨firstGuard, firstEqual⟩, secondGuard, secondEqual⟩ := both
  simp only [Resolved.Expr.eval_compare, Resolved.Expr.eval_column, constant] at firstEqual secondEqual
  have cellAccepted := Resolved.keyCellsEqual_of_accepted (affinity := some column.affinity) (collation := collation)
    (fun _ same => by obtain rfl := Option.some.inj same; exact (stored first firstMember).storedForm_getD columnAt)
    (fun _ same => by obtain rfl := Option.some.inj same; exact (stored second secondMember).storedForm_getD columnAt)
    firstEqual secondEqual
  have present : ∀ row : Row, row.values.getD index .null ≠ .null →
      row.values[index]? = some (row.values.getD index .null) := fun row nonNull => by
    cases cellAt : row.values[index]? <;> simp_all [List.getD_eq_getElem?_getD]
  have nonNull := cellAccepted
  simp only [LiteralData.keyCellsEqual, Bool.and_eq_true, bne_iff_ne] at nonNull
  have firstCell := present first nonNull.1.1
  have secondCell := present second nonNull.1.2
  have conflict : LiteralData.keyEqual key first second = true := by
    unfold LiteralData.keyEqual LiteralData.keyApplies
    simp only [filtered, oneTerm, List.all_cons, List.all_nil, LiteralData.termValue,
      LiteralData.read, firstCell, secondCell, cellAccepted, Bool.and_true, restricts _ firstGuard,
      restricts _ secondGuard]
  simp [conflict] at distinct

end Belay.Sqlite.Model
