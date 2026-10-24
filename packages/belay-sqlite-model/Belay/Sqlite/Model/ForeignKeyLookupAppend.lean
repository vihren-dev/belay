import Belay.Sqlite.Model.ForeignKeyParentUnique
import Belay.Sqlite.Model.StoreValueLaws

set_option doc.verso true

/-! Lookup changes when a fresh parent row is appended. -/

namespace Belay.Sqlite.Model

/-- For every key and child values, ordinary lookup in appended parent rows is the
disjunction of lookup in each list. Proof sketch: lookup is a list existential. -/
theorem parentFound_append (parent : CatalogTable) (key : ParentKey) (link : ForeignKeyLink)
    (values : List Value) (first rest : List Row) :
    parentFound parent key link values (first ++ rest) none =
      (parentFound parent key link values first none || parentFound parent key link values rest none) := by
  rw [parentFound_any parent key link values (first ++ rest), List.any_append]
  rw [← parentFound_any parent key link values first, ← parentFound_any parent key link values rest]

/-- For every located mapping, a parent scan that matches a child row implies that
none of the selected child values is NULL. The supplied key must equal the located key.
Proof sketch: each selected pair has a successful comparison, and no comparison accepts NULL. -/
theorem childMatches_not_null (child parent : CatalogTable) (link : ForeignKeyLink) (key : ParentKey)
    (position : Nat) (located : link.parent = .located position key) (parentRow childRow : Row)
    (matched : childMatches child parent link key parentRow childRow = true) :
    link.hasNull childRow.values = false := by
  simp only [ForeignKeyLink.hasNull, located, childValues, List.any_map, List.any_eq_false]
  intro selected member
  obtain ⟨index, below, atIndex⟩ := List.mem_iff_getElem.mp member
  have compared := List.all_eq_true.mp matched (selected, index) (by
    apply List.mem_iff_getElem.mpr
    refine ⟨index, by simpa using below, ?_⟩
    simp [List.getElem_zipIdx, atIndex])
  dsimp only at compared
  intro null
  have nullCell : childRow.values.getD selected .null = .null := by simpa using null
  simp only [nullCell, Resolved.comparisonOperands] at compared
  split at compared <;> simp [Value.store_null, LiteralData.keyCellsEqual, Resolved.numericOperand, Value.isText] at compared
  split at compared <;> simp at compared
/-- For every aligned present parent and link to it, appending a parent row makes
a child satisfied exactly when it was satisfied before or finds the new row.
Proof sketch: the unchanged catalog and {name}`parentFound_append` give the disjunction. -/
theorem ForeignKeyLink.satisfied_append_parent {database : Database} {position : Nat} {parent : Table}
    (present : database.table position = some parent) (aligned : position < database.rows.length)
    (link : ForeignKeyLink) (key : ParentKey) (located : link.parent = .located position key)
    (new row : Row) :
    link.satisfied (database.setRows position (parent.rows ++ [new])) row =
      (link.satisfied database row || parentFound parent.shape key link row.values [new] none) := by
  have atShape : database.catalog.tableAt position = some parent.shape := by
    obtain ⟨shape, atShape, same⟩ := Option.map_eq_some_iff.mp present
    subst parent
    exact atShape
  simp only [ForeignKeyLink.satisfied, located,
    show (database.setRows position (parent.rows ++ [new])).catalog = database.catalog from rfl,
    atShape, Database.rowsAt, Database.table_setRows _ present aligned, present,
    Option.map_some, Option.getD_some, parentFound_append]
  exact (Bool.or_assoc ..).symm

/-- For every aligned present parent, located link and stored new parent/child rows
with consistent lookup and scan comparisons, a child is unsatisfied after append exactly
when it was unsatisfied before and the new parent does not scan it.
Proof sketch: negate {name}`ForeignKeyLink.satisfied_append_parent` and use consistency. -/
theorem ForeignKeyLink.unsatisfied_append_parent {database : Database} {position : Nat} {parent : Table}
    (present : database.table position = some parent) (aligned : position < database.rows.length)
    (link : ForeignKeyLink) (key : ParentKey) (located : link.parent = .located position key)
    (child : CatalogTable) (new row : Row) (newStored : new.Stored parent.shape.columns)
    (childStored : row.Stored child.columns) (consistent : link.LookupScanConsistent child parent.shape key) :
    (!link.satisfied (database.setRows position (parent.rows ++ [new])) row) =
      (!link.satisfied database row && !childMatches child parent.shape link key new row) := by
  rw [ForeignKeyLink.satisfied_append_parent present aligned link key located new row]
  cases null : link.hasNull row.values with
  | true => simp [ForeignKeyLink.satisfied, null]
  | false =>
    rw [consistent new row newStored childStored null]
    exact Bool.not_or ..

/-- For every stored child matched by a fresh parent scan, if lookup and scan agree
and the enlarged parent table has distinct rowids and the selected unique key, that child
was unsatisfied before append. Proof sketch: a match is non-NULL and finds the new parent;
{name}`parentFound_fresh_no_old` excludes an old match. -/
theorem ForeignKeyLink.matching_new_parent_unsatisfied {database : Database} {position : Nat} {parent : Table}
    (present : database.table position = some parent) (link : ForeignKeyLink) (key : ParentKey)
    (located : link.parent = .located position key) (child : CatalogTable) (new row : Row)
    (newStored : new.Stored parent.shape.columns) (childStored : row.Stored child.columns)
    (consistent : link.LookupScanConsistent child parent.shape key) (keys : List UniqueKey)
    (unique : ({parent with rows := parent.rows ++ [new]} : Table).KeysUnique keys)
    (distinct : ({parent with rows := parent.rows ++ [new]} : Table).RowidsDistinct)
    (selectedUnique : ∀ pairs, key = .columns pairs → UniqueKey.ofColumns parent.shape.columns (pairs.map Prod.snd) ∈ keys)
    (matched : childMatches child parent.shape link key new row = true) :
    link.satisfied database row = false := by
  have null := childMatches_not_null child parent.shape link key position located new row matched
  have found : parentFound parent.shape key link row.values [new] none = true := by
    rw [consistent new row newStored childStored null] at matched
    exact matched
  have absent := parentFound_fresh_no_old parent.shape link key row.values parent.rows new keys unique distinct selectedUnique found
  have atShape : database.catalog.tableAt position = some parent.shape := by
    obtain ⟨shape, atShape, same⟩ := Option.map_eq_some_iff.mp present
    subst parent
    exact atShape
  simpa only [ForeignKeyLink.satisfied, null, Bool.false_or, located, atShape,
    Database.rowsAt, present, Option.map_some, Option.getD_some] using absent

end Belay.Sqlite.Model
