import Belay.Sqlite.Model.DatabaseLaws
import Belay.Sqlite.Model.ForeignKeyFacts

set_option doc.verso true

/-! ADD COLUMN and the comparison of a foreign key. The new cell is the last of each row of its
table, so a comparison that reads only the old cells gives the same result before and after. -/

namespace Belay.Sqlite.Model

/-- The child columns that a link reads: the selected projection of a located parent
({name}`childPositions`), else the declaration columns, as {name}`ForeignKeyLink.hasNull` reads
them. -/
def ForeignKeyLink.childReads (link : ForeignKeyLink) : List Nat :=
  match link.parent with
  | .located _ key => childPositions link key
  | .missing | .mismatch _ => link.key.columns

/-- Whether a parent key reads only the parent columns below the width: a rowid key reads no
column, and a key of columns reads the parent position of each pair. -/
def ParentKey.ReadsBelow (width : Nat) : ParentKey → Prop
  | .rowid => True
  | .columns pairs => ∀ pair ∈ pairs, pair.2 < width

/-- For every row cells, appended cells and position below the number of cells: reading the
position of the longer list gives the same cell. Proof sketch: an indexed lookup below the length
of the left list stays in the left list after appending. -/
theorem getD_append_below (values extra : List Value) {position : Nat} (below : position < values.length) :
    (values ++ extra).getD position .null = values.getD position .null := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left below]

/-- For every link, parent key, cells and appended cells: if every selected child position is below
the number of cells, the selected child values are the same for the longer list. Proof sketch: each
selected position reads the same cell ({name}`getD_append_below`). -/
theorem childValues_append (link : ForeignKeyLink) (key : ParentKey) (values extra : List Value)
    (below : ∀ position ∈ childPositions link key, position < values.length) :
    childValues link key (values ++ extra) = childValues link key values := by
  unfold childValues
  exact List.map_congr_left fun position member => getD_append_below values extra (below position member)

/-- For every link, cells and appended cells: if every child position that the link reads
({name}`ForeignKeyLink.childReads`) is below the number of cells, the NULL test of the link gives
the same result for the longer list. Proof sketch: the located case is
{name}`childValues_append`; the other case reads the declaration columns, each of which reads the
same cell. -/
theorem ForeignKeyLink.hasNull_append (link : ForeignKeyLink) (values extra : List Value)
    (below : ∀ position ∈ link.childReads, position < values.length) :
    link.hasNull (values ++ extra) = link.hasNull values := by
  unfold ForeignKeyLink.hasNull
  unfold ForeignKeyLink.childReads at below
  cases selected : link.parent with
  | located place key =>
    simp only [selected] at below
    dsimp only
    rw [childValues_append link key values extra below]
  | missing | mismatch _ =>
    simp only [selected] at below
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true]
    constructor <;> rintro ⟨position, member, same⟩ <;> refine ⟨position, member, ?_⟩
    · rwa [getD_append_below values extra (below position member)] at same
    · rwa [getD_append_below values extra (below position member)]

/-- For every database, link, row and appended cells: if every child position that the link reads
is below the number of cells of the row, the link is satisfied by the row with the cells appended
exactly when it is satisfied by the row. Proof sketch: the NULL test is
{name}`ForeignKeyLink.hasNull_append`, and the parent search reads the child cells through
{name}`childValues_append`. -/
theorem ForeignKeyLink.satisfied_append (database : Database) (link : ForeignKeyLink) (row : Row)
    (extra : List Value) (below : ∀ position ∈ link.childReads, position < row.values.length) :
    link.satisfied database (row.appendValues extra) = link.satisfied database row := by
  have null := link.hasNull_append row.values extra below
  unfold ForeignKeyLink.satisfied
  simp only [Row.appendValues, null]
  cases selected : link.parent with
  | missing | mismatch _ => rfl
  | located place key =>
    unfold ForeignKeyLink.childReads at below
    simp only [selected] at below
    dsimp only
    cases database.catalog.tableAt place with
    | none => rfl
    | some shape => simp only [parentFound, childValues_append link key row.values extra below]

/-- For every table entry, column, appended cells, parent key, pairs of child and parent positions,
child values and row: if the pairs read only parent columns below the width and the row has exactly
the width, the lookup of a row in the entry with the column appended, over the row with the cells
appended, gives the same result as over the row. Proof sketch: the pairs read the same column
definition and the same cell. -/
theorem indexHolds_appendColumn (shape : CatalogTable) (column : CatalogColumn) (extra : List Value)
    (pairs : List (Nat × Nat)) (values : List Value) (row : Row)
    (below : ∀ pair ∈ pairs, pair.2 < shape.columns.length) (wide : row.values.length = shape.columns.length) :
    indexHolds {shape with columns := shape.columns ++ [column]} pairs values (row.appendValues extra) =
      indexHolds shape pairs values row := by
  unfold indexHolds
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  refine forall_congr' fun entry => imp_congr_right fun member => ?_
  obtain ⟨⟨place, position⟩, value⟩ := entry
  have inside : position < shape.columns.length := below (place, position) (List.of_mem_zip member).1
  simp only [Row.appendValues, List.getElem?_append_left inside,
    getD_append_below row.values extra (wide ▸ inside)]

/-- For every table entry, column, appended cells, parent key, link, child values and rows: if the
key reads only parent columns below the width and every row has exactly the width, the parent
search over the rows with the cells appended, in the entry with the column appended, gives the same
result as over the rows. Proof sketch: a rowid key reads the unchanged rowids, and a key of columns
is {name}`indexHolds_appendColumn` for each row. -/
theorem parentFound_appendColumn (shape : CatalogTable) (column : CatalogColumn) (extra : List Value)
    (key : ParentKey) (link : ForeignKeyLink) (values : List Value) (rows : List Row)
    (below : key.ReadsBelow shape.columns.length) (wide : ∀ row ∈ rows, row.values.length = shape.columns.length) :
    parentFound {shape with columns := shape.columns ++ [column]} key link values
        (rows.map (·.appendValues extra)) none = parentFound shape key link values rows none := by
  cases key with
  | rowid => simp [parentFound, List.any_map, Function.comp_def, Row.appendValues]
  | columns pairs =>
    simp only [parentFound, Option.any_none, Bool.false_or, List.any_map, Function.comp_def]
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true]
    constructor <;> rintro ⟨row, member, holds⟩ <;> refine ⟨row, member, ?_⟩
    · rwa [indexHolds_appendColumn shape column extra pairs _ row below (wide row member)] at holds
    · rwa [indexHolds_appendColumn shape column extra pairs _ row below (wide row member)]

/-- For every database, target holding a table with wide rows, column, value, link and row: if the
link finds its parent in the target only through a key that reads parent columns below the width of
the table, the link is satisfied by the row after {name}`Database.addColumn` exactly when it is
satisfied before. The row is the same row, so this does not cover a child row of the target, which
gains a cell ({name}`ForeignKeyLink.satisfied_append`). A link whose parent is another table, a
missing parent or a mismatch requires nothing. Proof sketch: a parent other than the target keeps
its definition and rows; for the target, {name}`parentFound_appendColumn`. -/
theorem ForeignKeyLink.satisfied_addColumn (database : Database) (target : Nat) (column : CatalogColumn)
    (value : Value) {table : Table} (found : database.table target = some table) (wide : table.RowsWide)
    (link : ForeignKeyLink) (row : Row)
    (reads : ∀ key, link.parent = .located target key → key.ReadsBelow table.shape.columns.length) :
    link.satisfied (database.addColumn target column value) row = link.satisfied database row := by
  unfold ForeignKeyLink.satisfied
  cases selected : link.parent with
  | missing | mismatch _ => rfl
  | located place key =>
    dsimp only
    by_cases here : place = target
    · subst here
      have shape : database.catalog.tableAt place = some table.shape := by
        unfold Database.table at found
        cases old : database.catalog.tableAt place with
        | none => rw [old] at found; cases found
        | some _ => rw [old] at found; cases found; rfl
      have after := Catalog.tableAt_addColumn_same column shape
      have rows : (database.addColumn place column value).rowsAt place =
          table.rows.map (·.appendValues [Value.store column.affinity value]) := by
        simp [Database.rowsAt, Database.table_addColumn column value found, Table.appendColumns]
      have rowsOld : database.rowsAt place = table.rows := by simp [Database.rowsAt, found]
      change (link.hasNull row.values || match (database.catalog.addColumn place column).tableAt place with
        | some shape' => parentFound shape' key link row.values ((database.addColumn place column value).rowsAt place) none
        | none => false) = _
      rw [after, rows, rowsOld, shape]
      simp only [parentFound_appendColumn table.shape column [Value.store column.affinity value] key link
        row.values table.rows (reads key selected) wide]
    · have tableSame := Catalog.tableAt_addColumn_other database.catalog column here
      have rowsSame : (database.addColumn target column value).rowsAt place = database.rowsAt place := by
        simp only [Database.rowsAt, Database.table_addColumn_other database column value here]
      change (link.hasNull row.values || match (database.catalog.addColumn target column).tableAt place with
        | some shape' => parentFound shape' key link row.values ((database.addColumn target column value).rowsAt place) none
        | none => false) = _
      rw [tableSame, rowsSame]
      rfl

end Belay.Sqlite.Model
