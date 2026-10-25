import Belay.Sqlite.Model.GroupsPairwise
import Belay.Sqlite.Model.KeysUniqueLookup
import Belay.Sqlite.Model.DatabaseConstraintChecks

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every key containing a column term, two rows that conflict on the key have equal
values in that column under the term's collation. Missing cells and NULLs cannot conflict.
Proof sketch: select the column term from {name}`LiteralData.keyEqual_iff`. -/
theorem LiteralData.keyEqual_column {key : UniqueKey} {first second : Row}
    {position : Nat} {collation : Collation}
    (member : { term := .column position, collation } ∈ key.terms)
    (conflict : keyEqual key first second = true) :
    collation.compare (first.values.getD position .null) (second.values.getD position .null) = .eq := by
  obtain ⟨a, b, atFirst, atSecond, equal⟩ := (keyEqual_iff _ _ _).mp conflict |>.2.2 _ member
  simp only [termValue, read] at atFirst atSecond
  simp only [keyCellsEqual, Bool.and_eq_true, beq_iff_eq] at equal
  simpa [List.getD_eq_getElem?_getD, atFirst, atSecond] using equal.2

/-- For every table and key containing the given column under the given collation, if no
pair of source rows has equal values in that column, no pair conflicts on the key. This
also covers a filtered or multicolumn key containing that term. Proof sketch: each conflict
would give an equal column pair; scan order is a permutation and key conflict is symmetric. -/
theorem LiteralData.uniqueRows_of_pairwise_column (table : Table) {key : UniqueKey}
    {position : Nat} {collation : Collation}
    (member : { term := .column position, collation } ∈ key.terms)
    (distinct : (Resolved.sourceRows table).Pairwise fun first second =>
      collation.compare (second.getD position .null) (first.getD position .null) ≠ .eq) :
    uniqueRows key table.rows = true := by
  rw [uniqueRows_iff]
  have scan : table.scanRows.Pairwise fun first second => keyEqual key first second = false := by
    rw [Resolved.sourceRows, List.pairwise_map] at distinct
    apply distinct.imp
    intro first second unequal
    cases conflict : keyEqual key first second with
    | false => rfl
    | true => exact False.elim (unequal (keyEqual_column member (keyEqual_symm conflict)))
  apply (List.Perm.pairwise_iff (fun {first second} noConflict => ?_) table.scanRows_perm).mp scan
  cases conflict : keyEqual key second first with
  | false => rfl
  | true => have := keyEqual_symm conflict; simp [noConflict] at this

/-- For every table and key containing a column term, if grouping the source rows by that
column under the term's collation gives only groups of at most one row, the key has no
conflicting pair. This implication is one-way: GROUP BY combines NULLs, while a key lets
multiple NULLs pass. Proof sketch: {name}`Resolved.groups_short_iff_pairwise` gives distinct
column values, then {name}`LiteralData.uniqueRows_of_pairwise_column` excludes conflicts. -/
theorem LiteralData.uniqueRows_of_column_groups (table : Table) (context : Resolved.EvalContext)
    {key : UniqueKey} {position : Nat} {collation : Collation}
    (member : { term := .column position, collation } ∈ key.terms)
    (short : ∀ group ∈ Resolved.groups context [(.column position, collation)]
      (Resolved.sourceRows table), group.length ≤ 1) : uniqueRows key table.rows = true := by
  apply uniqueRows_of_pairwise_column table member
  have distinct := (Resolved.groups_short_iff_pairwise context [(.column position, collation)]
    (Resolved.sourceRows table)).mp short
  simpa [Resolved.sameGroup_single, Resolved.Expr.eval, Resolved.Expr.evaluate] using distinct

end Belay.Sqlite.Model
