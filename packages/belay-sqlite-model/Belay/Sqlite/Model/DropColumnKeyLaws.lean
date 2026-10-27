import Belay.Sqlite.Model.DropColumnFactLaws
import Belay.Sqlite.Model.Resolution.ColumnDropKeyLaws

set_option doc.verso true

/-! The unique keys of a table that lost a column (ADR 0019, D4): two rows without the cell conflict on a key
that does not read the column, changed by the drop, exactly when the rows conflict on the key. So a table whose
rows hold the keys keeps them. -/

namespace Belay.Sqlite.Model

/-- For every row, index and key term that does not read the column at the index: the value of the term after the
drop, over the row without the cell, is the value of the term over the row. Proof sketch: a column term reads the
cell that {name}`Row.dropValue_cell` finds at the moved position, and an expression term has one value
({lit}`Resolved.Expr.eval_dropColumn`). -/
theorem LiteralData.termValue_dropValue (row : Row) (index : Nat) {term : KeyTerm} (free : term.readsColumn index = false) :
    LiteralData.termValue (row.dropValue index) (term.dropColumn index) = LiteralData.termValue row term := by
  cases term with
  | column position =>
    have other : position ≠ index := by simpa [KeyTerm.readsColumn] using free
    simp [LiteralData.termValue, LiteralData.read, KeyTerm.dropColumn, Row.dropValue_cell, dropSource_dropPosition other]
  | expression value =>
    have free : value.readsColumn index = false := by simpa [KeyTerm.readsColumn] using free
    simp [LiteralData.termValue, KeyTerm.dropColumn, Row.dropValue,
      Resolved.Expr.eval_dropColumn _ (Resolved.EvalContext.plain_rowFree 0) index row.values free]

/-- For every row, index and key that does not read the column at the index: the key after the drop applies to the
row without the cell exactly when the key applies to the row. Proof sketch: the filter has one value
({lit}`Resolved.Expr.eval_dropColumn`). -/
theorem LiteralData.keyApplies_dropValue (row : Row) (index : Nat) {key : UniqueKey} (free : key.readsColumn index = false) :
    LiteralData.keyApplies (key.dropColumn index) (row.dropValue index) = LiteralData.keyApplies key row := by
  unfold LiteralData.keyApplies UniqueKey.dropColumn
  cases hfilter : key.filter with
  | none => rfl
  | some filter =>
    have free : filter.readsColumn index = false := by
      have both := free
      simp only [UniqueKey.readsColumn, hfilter, Option.map_some, Option.getD_some, Bool.or_eq_false_iff] at both
      exact both.2
    simp [Row.dropValue, Resolved.Expr.eval_dropColumn _ (Resolved.EvalContext.plain_rowFree 0) index row.values free]

/-- For every rows, index and key that does not read the column at the index: two rows without the cell conflict
on the key after the drop exactly when the rows conflict on the key. Proof sketch: the key applies to a row, and each
term has a value, as before ({name}`LiteralData.keyApplies_dropValue`, {name}`LiteralData.termValue_dropValue`). -/
theorem LiteralData.keyEqual_dropValue (first second : Row) (index : Nat) {key : UniqueKey} (free : key.readsColumn index = false) :
    LiteralData.keyEqual (key.dropColumn index) (first.dropValue index) (second.dropValue index) =
      LiteralData.keyEqual key first second := by
  have terms : ∀ term ∈ key.terms, term.term.readsColumn index = false := by
    intro term member
    have := free
    simp only [UniqueKey.readsColumn, Bool.or_eq_false_iff, List.any_eq_false] at this
    exact Bool.eq_false_iff.mpr fun h => this.1 term member h
  unfold LiteralData.keyEqual
  rw [LiteralData.keyApplies_dropValue first index free, LiteralData.keyApplies_dropValue second index free]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [UniqueKey.dropColumn, List.all_map, List.all_eq_true, Function.comp]
  refine forall_congr' fun term => imp_congr_right fun member => ?_
  simp only [IndexKey.dropColumn, LiteralData.termValue_dropValue first index (terms term member),
    LiteralData.termValue_dropValue second index (terms term member)]

/-- For every table with {name}`Table.KeysUnique` for some keys, every index, and keys that do not read the column at
the index: the table after the drop has {name}`Table.KeysUnique` for the keys changed by the drop. Proof sketch: the
rows after the drop are the rows without the cell, and two of them conflict on a key after the drop exactly when the
rows conflict on the key ({name}`LiteralData.keyEqual_dropValue`). -/
theorem Table.KeysUnique.dropColumn {keys : List UniqueKey} {table : Table} (unique : table.KeysUnique keys) (index : Nat)
    (free : ∀ key ∈ keys, key.readsColumn index = false) :
    (table.dropColumn index).KeysUnique (keys.map (UniqueKey.dropColumn index)) := by
  intro changed member
  obtain ⟨key, inKeys, rfl⟩ := List.mem_map.mp member
  simp only [Table.dropColumn, List.pairwise_map]
  exact (unique key inKeys).imp fun {first second} same => by
    rw [LiteralData.keyEqual_dropValue first second index (free key inKeys)]
    exact same

/-- For every catalog, position, index and table that can lose the column, when no index of the catalog reads it:
no unique key of the table reads the column. Proof sketch: a declared key names positions other than the index
({name}`CatalogTable.DropsCleanly`) and has no filter; the key of an index is read by no term or filter. -/
theorem Catalog.uniqueKeys_free {catalog : Catalog} {position index : Nat} {table : CatalogTable}
    (clean : table.DropsCleanly index)
    (indexes : ∀ object ∈ catalog, ∀ definition, object.entry = .index definition →
      definition.readsColumn position index = false) :
    ∀ key ∈ catalog.uniqueKeys position table, key.readsColumn index = false := by
  intro key member
  unfold Catalog.uniqueKeys at member
  rcases List.mem_append.mp member with declared | fromIndex
  · obtain ⟨keyPositions, inDeclared, rfl⟩ := List.mem_map.mp declared
    have other : ∀ p ∈ keyPositions, p ≠ index := by
      rcases List.mem_append.mp inDeclared with primary | keys
      · by_cases empty : table.primaryKey.isEmpty
        · simp [empty] at primary
        · simp only [empty, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at primary
          subst primary
          exact clean.primary
      · exact clean.keys keyPositions keys
    simp only [UniqueKey.readsColumn, UniqueKey.ofColumns, List.any_map, Option.map_none, Option.getD_none, Bool.or_false,
      List.any_eq_false, Function.comp, KeyTerm.readsColumn]
    intro p member
    simpa using other p member
  · obtain ⟨object, inCatalog, picked⟩ := List.mem_filterMap.mp fromIndex
    rcases object with ⟨name, entry⟩
    cases entry with
    | index definition =>
      have free := indexes ⟨name, .index definition⟩ inCatalog definition rfl
      simp only at picked
      split at picked
      · rename_i onTable
        cases picked
        have table : definition.table = position := by simpa using (Bool.and_eq_true_iff.mp onTable).1
        simpa [UniqueKey.readsColumn, CatalogIndex.readsColumn, CatalogIndex.uniqueKey, table] using free
      · simp at picked
    | table _ | view _ | trigger _ => simp at picked

end Belay.Sqlite.Model
