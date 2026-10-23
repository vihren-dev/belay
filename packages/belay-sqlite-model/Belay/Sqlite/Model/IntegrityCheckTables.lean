import Belay.Sqlite.Model.IntegrityCheckRows
import Belay.Sqlite.Model.IntegrityCheckIndexes
import Belay.Sqlite.Model.IntegrityCheckKeys

set_option doc.verso true

/-! The law of the check pragmas for one table (ADR 0019, D2): an admitted table gives no
failures exactly when {lit}`Table.NotNull`, {lit}`Table.TypesFit` and {lit}`Table.ChecksHold`
hold, and for {lit}`integrity_check` also {lit}`Table.KeysUnique` of its unique keys. -/

namespace Belay.Sqlite.Model

/-- For every condition, relation and list: the relation holds for every two items of the list
under the condition exactly when, under the condition, it holds for every two items.
Proof sketch: both sides are statements about every sublist of two items. -/
theorem pairwise_imp_iff {α} {condition : Prop} {relation : α → α → Prop} {items : List α} :
    items.Pairwise (fun a b => condition → relation a b) ↔ (condition → items.Pairwise relation) := by
  simp only [List.pairwise_iff_forall_sublist]
  constructor
  · intro all holds a b sub
    exact all sub holds
  · intro all a b sub holds
    exact all holds sub

/-- For every list of choices, relation for each choice and list: every two items are related
for every choice exactly when, for every choice, every two items are related.
Proof sketch: both sides are statements about every sublist of two items, with the quantifiers
swapped. -/
theorem pairwise_forall_iff {α β} {choices : List β} {relation : β → α → α → Prop} {items : List α} :
    items.Pairwise (fun a b => ∀ choice ∈ choices, relation choice a b) ↔
      ∀ choice ∈ choices, items.Pairwise (relation choice) := by
  simp only [List.pairwise_iff_forall_sublist]
  constructor
  · intro all choice member a b sub
    exact all sub choice member
  · intro all a b sub choice member
    exact all choice member sub

/-- For every table with {name}`Table.NotNull` and every row of it: at each position with a NOT
NULL column, the cell of the row, if any, is not NULL.
Proof sketch: it is {name}`Table.NotNull` at the row with the NULL cell. -/
theorem Table.NotNull.clean {table : Table} (notNull : table.NotNull) {row : Row} (member : row ∈ table.rows) :
    ∀ position column, table.shape.columns[position]? = some column → column.notNull = true →
      LiteralData.read row position ≠ some .null :=
  fun position column found marked cell => notNull row member position column .null found cell marked rfl

/-- For every table, quick flag, two rows and indexes, with the first row a row of a table with
{name}`Table.NotNull`: the rows are in order for integrity checking ({name}`Table.orderConflict`)
and their entries do not conflict in an index ({name}`Table.indexConflict`) exactly when both hold:

* without {lit}`quick`, in a {lit}`WITHOUT ROWID` table with a primary key, their primary keys
  are not equal ({name}`LiteralData.keyEqual`);
* without {lit}`quick`, for every index, their keys on it are not equal.
Proof sketch: the conflicts of the first row are the equal keys of the writes
({name}`entryConflict_eq_keyEqual`); a skipped order check has a NULL first key cell of the second
row, so the keys are not equal. -/
theorem Table.conflicts_iff {table : Table} (notNull : table.NotNull) (quick : Bool) (indexes : List CheckedIndex)
    {first second : Row} (member : first ∈ table.rows) :
    (table.orderConflict quick first second = false ∧
        ∀ checked ∈ indexes, table.indexConflict quick checked first second = false) ↔
      ((quick = false → table.shape.withoutRowid = true → table.shape.primaryKey ≠ [] →
          LiteralData.keyEqual (UniqueKey.ofColumns table.shape.columns table.shape.primaryKey) first second = false) ∧
        (quick = false → ∀ checked ∈ indexes, LiteralData.keyEqual checked.key first second = false)) := by
  have clean := notNull.clean member
  have order : table.orderConflict quick first second = false ↔ (quick = false → table.shape.withoutRowid = true →
      table.shape.primaryKey ≠ [] →
      LiteralData.keyEqual (UniqueKey.ofColumns table.shape.columns table.shape.primaryKey) first second = false) := by
    unfold Table.orderConflict
    dsimp only
    rw [entryConflict_eq_keyEqual _ _ _ _ clean]
    cases primary : table.shape.primaryKey with
    | nil => simp [orderSkipped, UniqueKey.ofColumns]
    | cons position rest =>
      cases skipped : orderSkipped (UniqueKey.ofColumns table.shape.columns (position :: rest)) second
      · cases quick <;> cases table.shape.withoutRowid <;> simp
      · simp only [orderSkipped, UniqueKey.ofColumns, List.map_cons, LiteralData.termValue, beq_iff_eq] at skipped
        have unequal : LiteralData.keyEqual (UniqueKey.ofColumns table.shape.columns (position :: rest)) first second =
            false := by
          simp only [LiteralData.keyEqual, UniqueKey.ofColumns, List.map_cons, List.all_cons, LiteralData.termValue,
            skipped]
          cases LiteralData.read first position <;> simp [LiteralData.keyCellsEqual]
        simp [unequal]
  have index : ∀ checked ∈ indexes, table.indexConflict quick checked first second = false ↔
      (quick = false → LiteralData.keyEqual checked.key first second = false) := by
    intro checked _
    unfold Table.indexConflict
    rw [entryConflict_eq_keyEqual _ _ _ _ clean]
    cases quick <;> simp
  rw [order]
  exact and_congr_right fun _ => ⟨fun all unquick checked found => (index checked found).mp (all checked found) unquick,
    fun all checked found => (index checked found).mpr fun unquick => all unquick checked found⟩

/-- For every catalog, position and table whose primary key is not empty: the primary key is in
{name}`Catalog.uniqueKeys` of the table.
Proof sketch: {name}`Catalog.uniqueKeys` starts with a primary key that is not empty. -/
theorem Catalog.primary_mem_uniqueKeys (catalog : Catalog) (position : Nat) {table : CatalogTable}
    (nonempty : table.primaryKey ≠ []) :
    UniqueKey.ofColumns table.columns table.primaryKey ∈ catalog.uniqueKeys position table := by
  unfold Catalog.uniqueKeys
  cases primary : table.primaryKey with
  | nil => exact absurd primary nonempty
  | cons _ _ => simp

/-- For every table whose primary key is not empty and has no index
({name}`CatalogTable.primaryIndexed`): the primary key is the rowid alias alone.
Proof sketch: {name}`CatalogTable.primaryIndexed` is false for a key that is not empty only when it
is the alias. -/
theorem CatalogTable.alias_of_not_indexed {table : CatalogTable} (nonempty : table.primaryKey ≠ [])
    (unindexed : table.primaryIndexed = false) : ∃ position, table.rowidAlias = some position ∧ table.primaryKey = [position] := by
  unfold CatalogTable.primaryIndexed at unindexed
  cases alias : table.rowidAlias with
  | none => cases primary : table.primaryKey <;> simp_all
  | some position => exact ⟨position, rfl, by cases primary : table.primaryKey <;> simp_all⟩

end Belay.Sqlite.Model
