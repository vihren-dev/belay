import Belay.Sqlite.Model.ForeignKeyCountDelete
import Belay.Sqlite.Model.KeysUniqueLookup

set_option doc.verso true

/-! A unique parent key prevents two parent rows from satisfying one child lookup. -/

namespace Belay.Sqlite.Model

/-- For every selected column mapping, child values and parent row, the index lookup
is the conjunction of the comparisons for those pairs, including duplicates.
Proof sketch: zip the mapped projection back to its original pairs. -/
theorem indexHolds_childValues (parent : CatalogTable) (link : ForeignKeyLink)
    (pairs : List (Nat × Nat)) (values : List Value) (row : Row) :
    indexHolds parent pairs (childValues link (.columns pairs) values) row =
      pairs.all (fun (child, position) => match parent.columns[position]? with
        | none => false
        | some column => LiteralData.keyCellsEqual (row.values.getD position .null)
            (Value.store (indexAffinity column) (values.getD child .null)) column.collation) := by
  simp only [indexHolds, childValues, childPositions, List.map_map, ← List.map_prod_left_eq_zip, List.all_map]
  rfl

/-- For every column mapping and two parent rows found by the same child values,
the rows conflict on the corresponding ordinary unique key. Missing parent columns
cannot satisfy a lookup. Proof sketch: each cell comparison is symmetric and transitive;
its non-NULL cells supply the values required by {name}`LiteralData.keyEqual_iff`. -/
theorem indexHolds_shared_keyEqual (parent : CatalogTable) (link : ForeignKeyLink)
    (pairs : List (Nat × Nat)) (values : List Value) (first second : Row)
    (left : indexHolds parent pairs (childValues link (.columns pairs) values) first = true)
    (right : indexHolds parent pairs (childValues link (.columns pairs) values) second = true) :
    LiteralData.keyEqual (UniqueKey.ofColumns parent.columns (pairs.map Prod.snd)) first second = true := by
  rw [indexHolds_childValues, List.all_eq_true] at left right
  rw [LiteralData.keyEqual_iff]
  refine ⟨rfl, rfl, ?_⟩
  intro term member
  simp only [UniqueKey.ofColumns, List.mem_map] at member
  obtain ⟨position, ⟨pair, inside, atPosition⟩, atTerm⟩ := member
  subst position
  subst term
  have a := left pair inside
  have b := right pair inside
  cases column : parent.columns[pair.2]? with
  | none => simp [column] at a
  | some found =>
    simp only [column] at a b
    have equal := LiteralData.keyCellsEqual_trans a (LiteralData.keyCellsEqual_symm b)
    have leftNonNull : first.values.getD pair.2 .null ≠ .null := by
      have nonnull := a
      simp only [LiteralData.keyCellsEqual, Bool.and_eq_true, bne_iff_ne] at nonnull
      exact nonnull.1.1
    have rightNonNull : second.values.getD pair.2 .null ≠ .null := by
      have nonnull := b
      simp only [LiteralData.keyCellsEqual, Bool.and_eq_true, bne_iff_ne] at nonnull
      exact nonnull.1.1
    have leftCell : first.values[pair.2]? = some (first.values.getD pair.2 .null) := by
      rw [List.getD_eq_getElem?_getD] at leftNonNull ⊢
      cases cell : first.values[pair.2]? with
      | none => simp only [cell, Option.getD_none, ne_eq, not_true_eq_false] at leftNonNull
      | some value => simp only [Option.getD_some]
    have rightCell : second.values[pair.2]? = some (second.values.getD pair.2 .null) := by
      rw [List.getD_eq_getElem?_getD] at rightNonNull ⊢
      cases cell : second.values[pair.2]? with
      | none => simp only [cell, Option.getD_none, ne_eq, not_true_eq_false] at rightNonNull
      | some value => simp only [Option.getD_some]
    exact ⟨_, _, leftCell, rightCell, by simpa [column] using equal⟩

/-- For every table with a newly appended row, if the enlarged table has distinct
rowids and unique keys, and a column mapping names one of those keys, a child that finds
the new row cannot also find an old row. A rowid mapping needs no key-membership premise.
Proof sketch: two matches contradict rowid distinctness or
{name}`indexHolds_shared_keyEqual` and uniqueness. -/
theorem parentFound_fresh_no_old (parent : CatalogTable) (link : ForeignKeyLink) (key : ParentKey)
    (values : List Value) (rows : List Row) (new : Row) (keys : List UniqueKey)
    (unique : ({shape := parent, rows := rows ++ [new]} : Table).KeysUnique keys)
    (distinct : ({shape := parent, rows := rows ++ [new]} : Table).RowidsDistinct)
    (selectedUnique : ∀ pairs, key = .columns pairs → UniqueKey.ofColumns parent.columns (pairs.map Prod.snd) ∈ keys)
    (found : parentFound parent key link values [new] none = true) :
    parentFound parent key link values rows none = false := by
  apply Bool.eq_false_iff.mpr
  intro previous
  rw [parentFound_any] at previous
  obtain ⟨old, member, matched⟩ := List.any_eq_true.mp previous
  cases key with
  | columns pairs =>
    have equal := indexHolds_shared_keyEqual parent link pairs values old new
      (by simpa [parentFound] using matched) (by simpa [parentFound] using found)
    have separate : LiteralData.keyEqual (UniqueKey.ofColumns parent.columns (pairs.map Prod.snd)) old new = false :=
      (unique _ (selectedUnique pairs rfl)).rel_of_mem_append member (by simp)
    rw [separate] at equal
    contradiction
  | rowid =>
    have separate : old.rowid ≠ new.rowid := by
      simp only [Table.RowidsDistinct, List.map_append, List.map_singleton] at distinct
      exact distinct.rel_of_mem_append (List.mem_map.mpr ⟨old, member, rfl⟩) (by simp)
    simp only [parentFound] at found matched
    split at found
    · rename_i rowid selected
      simp only [selected, Option.any_none, Bool.false_or, List.any_cons, List.any_nil,
        Bool.or_false, beq_iff_eq] at matched found
      exact separate (matched.trans found.symm)
    all_goals contradiction

end Belay.Sqlite.Model
