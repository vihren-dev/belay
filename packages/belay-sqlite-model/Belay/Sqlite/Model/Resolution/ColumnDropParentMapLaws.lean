import Belay.Sqlite.Model.Resolution.ColumnDropParentLaws

set_option doc.verso true

/-! The parent key of a foreign key whose child columns move (ADR 0019, D4). When a column of the child
table is dropped, the child columns of its foreign keys get new positions, and a parent key of columns holds the
child position of each pair. The parent that a key finds does not depend on those positions, so the key of the
moved child columns finds the same parent table and the same parent columns, with moved child positions. -/

namespace Belay.Sqlite.Model

/-- The parent key with each child position changed by the function. The parent columns and the rowid key stay. -/
def ParentKey.mapChildren (move : Nat → Nat) : ParentKey → ParentKey
  | .rowid => .rowid
  | .columns pairs => .columns (pairs.map fun (child, parent) => (move child, parent))

/-- The parent link with the child positions of its parent key changed by the function. -/
def ParentLink.mapChildren (move : Nat → Nat) : ParentLink → ParentLink
  | .located position key => .located position (key.mapChildren move)
  | .mismatch position => .mismatch position
  | .missing => .missing

/-- The foreign key with its child columns changed by the function. -/
def ForeignKey.mapColumns (move : Nat → Nat) (key : ForeignKey) : ForeignKey :=
  { key with columns := key.columns.map move }

/-- For every function, optional results and list: mapping the results of an optional function and collecting
them is collecting them and mapping the list. Proof sketch: induction over the list. -/
theorem List.mapM_option_map {α β γ : Type} (step : α → Option β) (change : β → γ) (items : List α) :
    items.mapM (fun item => (step item).map change) = (items.mapM step).map (List.map change) := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    cases hold : step item with
    | none => simp [List.mapM_cons, hold]
    | some value =>
      simp only [List.mapM_cons, hold, Option.map_some, ih]
      cases List.mapM step rest <;> simp

/-- For every optional place, lookup of a child by place, function and parent column: pairing the moved child with
the column is moving the child of the pair. Proof sketch: a case split on the place and on the lookup. -/
theorem option_bind_map_pair (found : Option Nat) (look : Nat → Option Nat) (move : Nat → Nat) (column : Nat) :
    (found.bind fun place => (Option.map move (look place)).bind fun child => some (child, column)) =
      found.bind ((Option.map fun pair => (move pair.fst, pair.snd)) ∘
        fun place => (look place).bind fun child => some (child, column)) := by
  cases found with
  | none => rfl
  | some place => cases hold : look place <;> simp [hold]

/-- For every parent table, key, function and index: the pairs of an index that the key of the moved child
columns names are the pairs that the key names, with the child positions moved. Proof sketch: the child of a pair
is the column of the key at the place of the referenced name, and the columns of the moved key are the columns
mapped, so each step of the collection maps its result ({name}`List.mapM_option_map`). -/
theorem matchIndex_mapColumns (parent : CatalogTable) (key : ForeignKey) (move : Nat → Nat)
    (index : List (Nat × Collation)) :
    matchIndex parent (key.mapColumns move) index =
      (matchIndex parent key index).map (List.map fun (child, column) => (move child, column)) := by
  unfold matchIndex
  simp only [ForeignKey.mapColumns, List.length_map]
  by_cases lengths : (index.length != key.columns.length) = true
  · simp [lengths]
  · simp only [lengths, Bool.false_eq_true, ↓reduceIte]
    rw [← List.mapM_option_map]
    congr 1
    funext entry
    obtain ⟨column, collation⟩ := entry
    cases parent.columns[column]? with
    | none => simp
    | some definition =>
      by_cases same : collation = definition.collation
      · subst same
        simp [List.getElem?_map]
        exact option_bind_map_pair _ _ _ _
      · simp [same]

/-- For every list, optional function and function: the first result of the mapped results is the first result,
mapped. Proof sketch: induction over the list. -/
theorem List.findSome?_option_map {α β γ : Type} (step : α → Option β) (change : β → γ) (items : List α) :
    items.findSome? (fun item => (step item).map change) = (items.findSome? step).map change := by
  induction items with
  | nil => simp
  | cons item rest ih => cases hold : step item <;> simp [hold, ih]

/-- For every indexes, child columns and function: the parent key of the primary key that pairs the child
columns with the parent columns pairs the moved child columns with them, when the key is found. Proof sketch:
{lit}`List.zip_map_left`. -/
theorem primaryKey_zip_mapColumns (indexes : List (Bool × List (Nat × Collation))) (columns : List Nat)
    (move : Nat → Nat) :
    ((indexes.find? (·.1)).bind fun entry =>
        if entry.2.length = columns.length then
          some (ParentKey.columns ((columns.map move).zip (entry.2.map (·.1)))) else none) =
      ((indexes.find? (·.1)).bind fun entry =>
        if entry.2.length = columns.length then some (ParentKey.columns (columns.zip (entry.2.map (·.1)))) else none).map
          (ParentKey.mapChildren move) := by
  cases indexes.find? (·.1) with
  | none => rfl
  | some found =>
    by_cases lengths : found.2.length = columns.length
    · simp [lengths, ParentKey.mapChildren, List.zip_map_left]
    · simp [lengths]

/-- For every list, lookup of the pairs of a parent key and function: the first parent key of columns whose child
positions were moved is the first parent key of columns, moved. Proof sketch: {name}`List.findSome?_option_map`. -/
theorem findSome?_columns_map {α : Type} (items : List α) (look : α → Option (List (Nat × Nat))) (move : Nat → Nat) :
    items.findSome? (fun item => (look item).map fun pairs =>
        ParentKey.columns (pairs.map fun pair => (move pair.1, pair.2))) =
      (items.findSome? fun item => (look item).map ParentKey.columns).map (ParentKey.mapChildren move) := by
  rw [← List.findSome?_option_map]
  congr 1
  funext item
  cases look item <;> rfl

/-- For every catalog, position, parent table, key and function: the parent key of the key of the moved child
columns is the parent key of the key, with the child positions moved. Proof sketch: the choice reads the child
columns only by their number and by the place of a referenced name; the rowid key and the key of the primary key
are decided by the number, the pairs of the primary key zip the child columns, and the pairs of a named key come
from {name}`matchIndex_mapColumns`. -/
theorem Catalog.parentKey_mapColumns (catalog : Catalog) (position : Nat) (parent : CatalogTable)
    (key : ForeignKey) (move : Nat → Nat) :
    catalog.parentKey position parent (key.mapColumns move) =
      (catalog.parentKey position parent key).map (ParentKey.mapChildren move) := by
  obtain ⟨table, columns, referenced, onDelete, onUpdate, deferred⟩ := key
  unfold Catalog.parentKey
  simp only [ForeignKey.mapColumns, List.length_map]
  split <;> simp_all [ParentKey.mapChildren, Function.comp_def]
  all_goals
    have e : ∀ R, ForeignKey.mk table (columns.map move) R onDelete onUpdate deferred =
        ForeignKey.mapColumns move (ForeignKey.mk table columns R onDelete onUpdate deferred) := fun _ => rfl
    try simp only [e, matchIndex_mapColumns, Option.map_map, Function.comp_def]
  all_goals
    split <;> rename_i condition <;> simp [ParentKey.mapChildren, primaryKey_zip_mapColumns, findSome?_columns_map]

/-- For every catalog, key and function: the parent that the key of the moved child columns finds is the parent
that the key finds, with the child positions moved. Proof sketch: the lookup of the parent table reads the name of
the key only, and the parent key is {name}`Catalog.parentKey_mapColumns`. -/
theorem Catalog.parentLink_mapColumns (catalog : Catalog) (key : ForeignKey) (move : Nat → Nat) :
    catalog.parentLink (key.mapColumns move) = (catalog.parentLink key).mapChildren move := by
  unfold Catalog.parentLink
  simp only [show (key.mapColumns move).table = key.table from rfl, Catalog.parentKey_mapColumns]
  cases hold : catalog.findTable key.table with
  | none =>
    cases view : catalog.findView key.table with
    | none => simp [ParentLink.mapChildren]
    | some found => simp [ParentLink.mapChildren]
  | some found =>
    cases hkey : catalog.parentKey found.1 found.2 key <;> simp [ParentLink.mapChildren, hkey]

/-- For every catalog, position of a table, index, key that does not name that table, and function: the parent that
the key of the moved child columns finds after the drop is the parent that the key finds before it, with the child
positions moved. Proof sketch: {name}`Catalog.parentLink_dropColumn` for the moved key, which names the same
table, then {name}`Catalog.parentLink_mapColumns`. -/
theorem Catalog.parentLink_dropColumn_mapColumns (catalog : Catalog) {position : Nat} (index : Nat)
    {object : CatalogObject} (at_position : catalog[position]? = some object) (key : ForeignKey)
    (other : key.table.sameName object.name = false) (move : Nat → Nat) :
    (catalog.dropColumn position index).parentLink (key.mapColumns move) = (catalog.parentLink key).mapChildren move := by
  rw [Catalog.parentLink_dropColumn catalog index at_position (key.mapColumns move) other,
    Catalog.parentLink_mapColumns]

end Belay.Sqlite.Model
