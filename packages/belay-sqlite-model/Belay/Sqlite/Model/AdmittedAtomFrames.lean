import Belay.Sqlite.Model.DatabaseFacts
import Belay.Sqlite.Model.OutlineDatabaseLaws
import Belay.Sqlite.Model.TableAtomFrames
import Belay.Sqlite.Model.DropColumnFactLaws

set_option doc.verso true

/-! The frame lemmas of the five table atoms of {lit}`Database.Admitted` (ADR 0022, D3, slice 4):
"rowids distinct", "rowids in range", "rows wide", "rows stored" and "rows aliased". Each atom
says a fact of the rows of one table with its catalog entry, so a table whose rows are rows of a
table that satisfies the atom, with the same part of the entry, satisfies it. "Rowids distinct" also
needs the rows to be a sublist, because a repeated row would repeat its rowid. {lit}`TableAtom`
supplies the shared empty, sublist, rename and column-drop contract below these instances. -/

namespace Belay.Sqlite.Model

/-- The frame lemma of {name}`Table.RowidsDistinct`, for every two tables: if the first satisfies
it and the rows of the second are a sublist of the rows of the first, the second satisfies it. The
entries can differ. Proof sketch: the rowids of a sublist are a sublist of the rowids, and a
sublist of a list without repeats has none ({name}`List.Nodup.sublist`). -/
theorem Table.RowidsDistinct.frame {table other : Table} (distinct : table.RowidsDistinct)
    (sublist : other.rows.Sublist table.rows) : other.RowidsDistinct :=
  distinct.sublist (sublist.map Row.rowid)

/-- The frame lemma of {name}`Table.RowidsInRange`, for every two tables: if the first satisfies
it and each row of the second is a row of the first, the second satisfies it. The entries can
differ. Proof sketch: the rowid of a row of the second is the rowid of the same row of the first. -/
theorem Table.RowidsInRange.frame {table other : Table} (inRange : table.RowidsInRange)
    (rows : ∀ row ∈ other.rows, row ∈ table.rows) : other.RowidsInRange :=
  fun row member => inRange row (rows row member)

/-- The frame lemma of {name}`Table.RowsWide`, for every two tables: if the first satisfies it, each
row of the second is a row of the first, and the second has as many columns as the first, the second
satisfies it. Proof sketch: a row of the second is a row of the first, whose width is the width of
the first, which is the width of the second. -/
theorem Table.RowsWide.frame {table other : Table} (wide : table.RowsWide)
    (rows : ∀ row ∈ other.rows, row ∈ table.rows) (columns : other.shape.columns.length = table.shape.columns.length) :
    other.RowsWide :=
  fun row member => (wide row (rows row member)).trans columns.symm

/-- The frame lemma of {name}`Table.RowsStored`, for every two tables: if the first satisfies it,
each row of the second is a row of the first, and the second has the same columns, the second
satisfies it. Proof sketch: a row of the second is a row of the first, which is stored for the same
columns. -/
theorem Table.RowsStored.frame {table other : Table} (stored : table.RowsStored)
    (rows : ∀ row ∈ other.rows, row ∈ table.rows) (columns : other.shape.columns = table.shape.columns) :
    other.RowsStored :=
  fun row member => columns ▸ stored row (rows row member)

/-- The frame lemma of {name}`Table.RowsAliased`, for every two tables: if the first satisfies it,
each row of the second is a row of the first, and the second has the same rowid alias, the second
satisfies it. Proof sketch: a row of the second is a row of the first, which is aliased for the
same alias. -/
theorem Table.RowsAliased.frame {table other : Table} (aliased : table.RowsAliased)
    (rows : ∀ row ∈ other.rows, row ∈ table.rows) (alias : other.shape.rowidAlias = table.shape.rowidAlias) :
    other.RowsAliased :=
  fun row member => alias ▸ aliased row (rows row member)

/-- "Rowids distinct" is a {name}`TableAtom`. Proof sketch: no rows have no rowids to repeat;
{name}`Table.RowidsDistinct.frame` gives the sublist. -/
theorem Table.rowidsDistinctAtom : TableAtom Table.RowidsDistinct where
  empty table none := by simp [Table.RowidsDistinct, none]
  sublist _ _ distinct _ sub := distinct.frame sub
  renamed _ _ distinct rows _ := by simpa [Table.RowidsDistinct, rows] using distinct
  dropped _ _ distinct _ := distinct.dropColumn _

/-- "Rowids in range" is a {name}`TableAtom`. Proof sketch: no rows leave nothing to check; a
sublist has only rows of the first table ({name}`Table.RowidsInRange.frame`). -/
theorem Table.rowidsInRangeAtom : TableAtom Table.RowidsInRange where
  empty table none := fun row member => by simp [none] at member
  sublist _ _ inRange _ sub := inRange.frame fun _ member => sub.subset member
  renamed _ _ inRange rows _ := by simpa [Table.RowidsInRange, rows] using inRange
  dropped _ _ inRange _ := inRange.dropColumn _

/-- "Rows wide" is a {name}`TableAtom`. Proof sketch: no rows leave nothing to check; a sublist has
only rows of the first table, and the same entry has the same columns
({name}`Table.RowsWide.frame`). -/
theorem Table.rowsWideAtom : TableAtom Table.RowsWide where
  empty table none := fun row member => by simp [none] at member
  sublist _ _ wide same sub := wide.frame (fun _ member => sub.subset member) (by rw [same])
  renamed _ _ wide rows same := wide.of_blankNames rows same
  dropped _ _ wide clean := wide.dropColumn clean.inside

/-- "Rows stored" is a {name}`TableAtom`. Proof sketch: as {name}`Table.rowsWideAtom`, with
{name}`Table.RowsStored.frame`. -/
theorem Table.rowsStoredAtom : TableAtom Table.RowsStored where
  empty table none := fun row member => by simp [none] at member
  sublist _ _ stored same sub := stored.frame (fun _ member => sub.subset member) (by rw [same])
  renamed _ _ stored rows same := stored.of_blankNames rows same
  dropped _ _ stored _ := stored.dropColumn _

/-- "Rows aliased" is a {name}`TableAtom`. Proof sketch: as {name}`Table.rowsWideAtom`, with
{name}`Table.RowsAliased.frame`. -/
theorem Table.rowsAliasedAtom : TableAtom Table.RowsAliased where
  empty table none := fun row member => by simp [none] at member
  sublist _ _ aliased same sub := aliased.frame (fun _ member => sub.subset member) (by rw [same])
  renamed _ _ aliased rows same := aliased.of_blankNames rows same
  dropped _ _ aliased clean := aliased.dropColumn clean.alias

end Belay.Sqlite.Model
