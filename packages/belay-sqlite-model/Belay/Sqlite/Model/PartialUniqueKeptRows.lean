import Belay.Sqlite.Model.DuplicateKeyQuery
import Belay.Sqlite.Model.KeysUniqueLookup
import Belay.Sqlite.Model.QueryLaws

set_option doc.verso true

/-!
A unique index and a filtered duplicate-key query (ADR 0017, S6). A unique index on one column
with a filter {lit}`w` allows no two rows for which {lit}`w` is true and the column values are
equal under the collation of the index, when the column is NOT NULL. This is the table fact that
makes the query {lit}`SELECT c FROM t WHERE w GROUP BY k HAVING count(*) > 1` return no row: its
groups ({lit}`Resolved.keptRows` and {lit}`Resolved.groups`) have one row each.
-/

namespace Belay.Sqlite.Model

/-- For every table, keys, key, column position, collation, column, evaluation context and optional
guard: assume that all of these hold.
* The table satisfies {name}`Table.KeysUnique` for the keys, {name}`Table.RowsWide` and
  {name}`Table.NotNull`.
* The key is one of the keys, and its one term is the column at the position under the collation.
* The column at the position is declared NOT NULL.
* The guard implies the filter of the key: every row for which the guard is true (a missing guard is
  true) is a row for which the filter of the key is true (a missing filter is true), where the filter
  is read with the plain context.

Then no two rows of the table that the guard keeps ({name}`Resolved.keptRows` of
{name}`Resolved.sourceRows`, in scan order) have values at the position that compare equal under the
collation. A row for which the guard is false or NULL is not kept, so it can repeat a value. The
premises are checkable about a database: the first three hold in a valid database for a unique index
or UNIQUE constraint, and the guard is the {lit}`WHERE` of the query. Proof sketch: scan order is a
permutation of the rows ({name}`Table.scanRows_perm`) and a conflict is symmetric
({name}`LiteralData.keyEqual_symm`), so the pairwise fact of the table holds in scan order. Two kept
rows with equal values would conflict on the key: the filter is true for both, and both values are
present and not NULL. -/
theorem Table.KeysUnique.keptRows_pairwise {keys : List UniqueKey} {table : Table}
    (unique : table.KeysUnique keys) (wide : table.RowsWide) (notNull : table.NotNull)
    {key : UniqueKey} (member : key ∈ keys) {index : Nat} {descending : Bool} {collation : Collation}
    (oneTerm : key.terms = [{ term := .column index, descending, collation }])
    {column : CatalogColumn} (columnAt : table.shape.columns[index]? = some column)
    (declaredNotNull : column.notNull = true) (context : Resolved.EvalContext) (guard : Option Resolved.Expr)
    (restricts : ∀ row : List Value, (guard.all fun condition => Resolved.truthy (condition.eval context row)) = true →
      (key.filter.all fun filter => Resolved.truthy (filter.eval (.plain 0) row)) = true) :
    (Resolved.keptRows context guard (Resolved.sourceRows table)).Pairwise fun earlier later =>
      collation.compare (later.getD index .null) (earlier.getD index .null) ≠ .eq := by
  have symmetric : ∀ {first second : Row}, LiteralData.keyEqual key first second = false →
      LiteralData.keyEqual key second first = false := fun {first second} noConflict => by
    cases conflict : LiteralData.keyEqual key second first with
    | false => rfl
    | true => have := LiteralData.keyEqual_symm conflict; simp [noConflict] at this
  have scan := (List.Perm.pairwise_iff symmetric table.scanRows_perm).mpr (unique key member)
  have present : ∀ row ∈ table.scanRows, ∃ value, row.values[index]? = some value ∧ value ≠ .null := fun row inRows => by
    have inTable := table.scanRows_perm.mem_iff.mp inRows
    obtain ⟨value, atIndex⟩ : ∃ value, row.values[index]? = some value :=
      ⟨_, List.getElem?_eq_getElem (by have := wide row inTable; have := (List.getElem?_eq_some_iff.mp columnAt).1; omega)⟩
    exact ⟨value, atIndex, notNull row inTable index column value columnAt atIndex declaredNotNull⟩
  rw [Resolved.keptRows, Resolved.sourceRows, List.filter_map, List.pairwise_map, List.pairwise_filter]
  refine scan.imp_of_mem fun {first second} firstIn secondIn noConflict firstKept secondKept same => ?_
  obtain ⟨firstValue, firstAt, firstNonNull⟩ := present first firstIn
  obtain ⟨secondValue, secondAt, secondNonNull⟩ := present second secondIn
  have applies : ∀ row : Row, ((fun row => Option.all (fun condition =>
        Resolved.truthy (Resolved.Expr.eval context row condition)) guard) ∘ Row.values) row = true →
      LiteralData.keyApplies key row = true := fun row kept => by
    have := restricts row.values kept
    unfold LiteralData.keyApplies
    cases filter : key.filter <;> simp_all
  simp only [List.getD_eq_getElem?_getD, firstAt, secondAt, Option.getD_some] at same
  have conflict : LiteralData.keyEqual key first second = true := by
    rw [LiteralData.keyEqual_iff]
    refine ⟨applies first firstKept, applies second secondKept, fun term termMember => ?_⟩
    rw [oneTerm, List.mem_singleton] at termMember
    subst termMember
    refine ⟨firstValue, secondValue, firstAt, secondAt, ?_⟩
    simp only [LiteralData.keyCellsEqual, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
    exact ⟨⟨firstNonNull, secondNonNull⟩, Std.OrientedCmp.eq_symm same⟩
  simp [conflict] at noConflict

end Belay.Sqlite.Model
