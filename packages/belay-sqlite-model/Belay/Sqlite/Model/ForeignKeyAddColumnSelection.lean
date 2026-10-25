import Belay.Sqlite.Model.CatalogAddColumnSearch

set_option doc.verso true

/-! ADD COLUMN and the selection of a parent key. The new column is the last of its table, so a
foreign key that already selects its parent key selects it again, as long as the selection
reads only the old columns. -/

namespace Belay.Sqlite.Model

/-- For every catalog, position, table entry and column: if every column position of every parent
index of the entry is below its width, the parent indexes of the entry with the column appended are
the same. Proof sketch: only the collation lookups read the columns, and a position below the width
reads the same column. -/
theorem Catalog.parentIndexes_appendColumn (catalog : Catalog) (position : Nat) (shape : CatalogTable)
    (column : CatalogColumn)
    (below : ∀ entry ∈ catalog.parentIndexes position shape, ∀ pair ∈ entry.2, pair.1 < shape.columns.length) :
    catalog.parentIndexes position {shape with columns := shape.columns ++ [column]} =
      catalog.parentIndexes position shape := by
  have cols : ∀ positions : List Nat, (∀ place ∈ positions, place < shape.columns.length) →
      positions.map (fun place => (place, ((shape.columns ++ [column])[place]?.map (·.collation)).getD Collation.binary)) =
        positions.map (fun place => (place, (shape.columns[place]?.map (·.collation)).getD Collation.binary)) := by
    intro positions inside
    apply List.map_congr_left
    intro place member
    simp [List.getElem?_append_left (inside place member)]
  unfold Catalog.parentIndexes at below ⊢
  simp only [] at below ⊢
  have unique : ∀ key ∈ shape.uniqueKeys, ∀ place ∈ key, place < shape.columns.length := by
    intro key member place inside
    exact below (false, List.map _ key)
      (by simp only [List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨key, member, rfl⟩))
      (place, _) (List.mem_map.mpr ⟨place, inside, rfl⟩)
  have uniques : shape.uniqueKeys.map (fun key => (false, key.map fun place =>
      (place, ((shape.columns ++ [column])[place]?.map (·.collation)).getD Collation.binary))) =
      shape.uniqueKeys.map (fun key => (false, key.map fun place =>
        (place, (shape.columns[place]?.map (·.collation)).getD Collation.binary))) :=
    List.map_congr_left fun key member => by rw [cols key (unique key member)]
  rw [uniques]
  congr 2
  split
  · rfl
  · rename_i notEmpty
    have bound : ∀ place ∈ shape.primaryKey, place < shape.columns.length := by
      intro place member
      refine below (true, shape.primaryKey.map fun place =>
        (place, (shape.columns[place]?.map (·.collation)).getD Collation.binary)) ?_ (place, _)
        (List.mem_map.mpr ⟨place, member, rfl⟩)
      simp [notEmpty]
    rw [cols shape.primaryKey bound]

/-- For every two functions and list: if the functions agree on every element, mapping the list in
{name}`Option` with either gives the same result. Proof sketch: induction on the list. -/
theorem mapM_option_congr {α β} (first second : α → Option β) :
    ∀ (items : List α), (∀ item ∈ items, first item = second item) → items.mapM first = items.mapM second
  | [], _ => rfl
  | item :: rest, same => by
    simp only [List.mapM_cons, same item (by simp),
      mapM_option_congr first second rest fun other member => same other (by simp [member])]

/-- For every two functions and list: if the functions agree on every element, the first result
of {name}`List.findSome?` with either is the same. Proof sketch: induction on the list. -/
theorem findSome?_option_congr {α β} (first second : α → Option β) :
    ∀ (items : List α), (∀ item ∈ items, first item = second item) → items.findSome? first = items.findSome? second
  | [], _ => rfl
  | item :: rest, same => by
    simp only [List.findSome?_cons, same item (by simp),
      findSome?_option_congr first second rest fun other member => same other (by simp [member])]

/-- For every table entry, column, foreign key and parent index whose column positions are all
below the width of the entry: matching the key to the index in the entry with the column appended
({name}`matchIndex`) gives the same result. Proof sketch: matching reads the parent columns only
through the index positions, and a position below the width reads the same column. -/
theorem matchIndex_appendColumn (shape : CatalogTable) (column : CatalogColumn) (key : ForeignKey)
    (index : List (Nat × Collation)) (below : ∀ pair ∈ index, pair.1 < shape.columns.length) :
    matchIndex {shape with columns := shape.columns ++ [column]} key index = matchIndex shape key index := by
  unfold matchIndex
  split
  · rfl
  · apply mapM_option_congr
    intro pair member
    obtain ⟨place, collation⟩ := pair
    simp [List.getElem?_append_left (below _ member)]

/-- The condition for a located parent to keep its key when a column is appended to it: its rowid
alias, if any, is a column, and each column position of each parent index
({name}`Catalog.parentIndexes`) is below its width. Without it the new column could become the alias
or a column of an index. -/
def CatalogTable.SelectionBelow (catalog : Catalog) (position : Nat) (shape : CatalogTable) : Prop :=
  (∀ alias, shape.rowidAlias = some alias → alias < shape.columns.length) ∧
    ∀ entry ∈ catalog.parentIndexes position shape, ∀ pair ∈ entry.2, pair.1 < shape.columns.length

/-- For every two catalogs, position, table entry, column and foreign key: if the parent indexes of
the entry with the column appended in the second catalog are those of the entry in the first, and the
selection reads only columns below the width ({name}`CatalogTable.SelectionBelow`), the parent key of
the key in the entry with the column appended is the parent key of the key in the entry. Proof
sketch: the alias test and the index search ({name}`matchIndex_appendColumn`) read the same
columns. -/
theorem Catalog.parentKey_appendColumn (catalog next : Catalog) (position : Nat) (shape : CatalogTable)
    (column : CatalogColumn) (key : ForeignKey)
    (indexes : next.parentIndexes position {shape with columns := shape.columns ++ [column]} =
      catalog.parentIndexes position shape)
    (below : shape.SelectionBelow catalog position) :
    next.parentKey position {shape with columns := shape.columns ++ [column]} key =
      catalog.parentKey position shape key := by
  unfold Catalog.parentKey
  simp only [indexes]
  have rest : ∀ named : Bool, (if (key.columns.length == 1 && named) = true then some ParentKey.rowid else
      if key.referenced.isEmpty = true then
        (List.find? (fun x => x.fst) (catalog.parentIndexes position shape)).bind fun x =>
          if (x.snd.length == key.columns.length) = true then
            some (ParentKey.columns (key.columns.zip (List.map (fun x => x.fst) x.snd)))
          else none
      else Option.map ParentKey.columns
        (List.findSome? (fun x => matchIndex {shape with columns := shape.columns ++ [column]} key x.snd)
          (catalog.parentIndexes position shape))) =
      (if (key.columns.length == 1 && named) = true then some ParentKey.rowid else
      if key.referenced.isEmpty = true then
        (List.find? (fun x => x.fst) (catalog.parentIndexes position shape)).bind fun x =>
          if (x.snd.length == key.columns.length) = true then
            some (ParentKey.columns (key.columns.zip (List.map (fun x => x.fst) x.snd)))
          else none
      else Option.map ParentKey.columns
        (List.findSome? (fun x => matchIndex shape key x.snd) (catalog.parentIndexes position shape))) := by
    intro named
    have search : List.findSome? (fun x => matchIndex {shape with columns := shape.columns ++ [column]} key x.snd)
        (catalog.parentIndexes position shape) =
        List.findSome? (fun x => matchIndex shape key x.snd) (catalog.parentIndexes position shape) :=
      findSome?_option_congr _ _ _ fun entry member => matchIndex_appendColumn shape column key entry.2 (below.2 entry member)
    rw [search]
  cases found : shape.rowidAlias with
  | none => simpa [found] using rest false
  | some alias =>
    have same := List.getElem?_append_left (l₂ := [column]) (below.1 alias found)
    cases referenced : key.referenced with
    | nil => simp
    | cons name more =>
      cases more with
      | nil => simpa [found, referenced, same] using rest _
      | cons other more => simpa [found, referenced] using rest false

/-- For every catalog, target, column and foreign key: if the table at the target meets
{name}`CatalogTable.SelectionBelow`, the key selects the same parent link after
{name}`Catalog.addColumn`: the same table, or none, and the same parent key, or none. The new
column is the last column of its table and the name search is unchanged, so only a position
at or above the old width could change the selection. Proof sketch: the found table is the old one
with the column appended at the target ({name}`Catalog.findTable_addColumn`), and the view lookup is unchanged ({name}`Catalog.findView_addColumn`); the parent key is the
same by {name}`Catalog.parentKey_appendColumn`, or by {name}`Catalog.parentIndexes_addColumn` for
another position. -/
theorem Catalog.parentLink_addColumn (catalog : Catalog) (target : Nat) (column : CatalogColumn) (key : ForeignKey)
    (below : ∀ shape, catalog.tableAt target = some shape → shape.SelectionBelow catalog target) :
    (catalog.addColumn target column).parentLink key = catalog.parentLink key := by
  unfold Catalog.parentLink
  rw [Catalog.findTable_addColumn]
  cases found : catalog.findTable key.table with
  | none => simp [Catalog.findView_addColumn]
  | some pair =>
    obtain ⟨position, shape⟩ := pair
    obtain ⟨object, atPosition, entry, _⟩ := Catalog.findTable_some catalog _ _ _ found
    have present : catalog.tableAt position = some shape := by
      obtain ⟨_, objectEntry⟩ := object
      cases entry
      simp [Catalog.tableAt, atPosition]
    by_cases here : position = target
    · subst here
      simp only [Option.map_some, present, Option.isSome_some, and_self, ite_true]
      rw [Catalog.parentKey_appendColumn catalog (catalog.addColumn position column) position shape column key
        (by rw [Catalog.parentIndexes_addColumn, Catalog.parentIndexes_appendColumn catalog position shape column
          (below shape present).2]) (below shape present)]
    · simp only [Option.map_some, here, false_and, ite_false]
      unfold Catalog.parentKey
      simp only [Catalog.parentIndexes_addColumn]

end Belay.Sqlite.Model
