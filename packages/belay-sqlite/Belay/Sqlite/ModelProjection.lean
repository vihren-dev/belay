import Belay.Sqlite.ModelFacts

set_option doc.verso true

/-! NULL extension is a structural projection fact, independent of observation contracts. -/

namespace Belay.Sqlite

/-- Retain rowids and row order, replacing each row's cells with one observed
{name}`Value.null`. Use this for the expected projection of a new nullable field;
{assert}`nullExtension [] = []`. The input cells do not affect the result. -/
def nullExtension (rows : List (Int × List (Option Value))) : List (Int × List (Option Value)) :=
  rows.map fun row => (row.1, [some .null])

/-- For every test, list and item: if {name}`findPosition` finds nothing in the
list and the test accepts the item, it finds the item after the list. -/
theorem findPosition_append_none {test : α → Bool} {items : List α} (absent : findPosition test items = none)
    (accepted : test item = true) : findPosition test (items ++ [item]) = some (items.length, item) := by
  induction items with
  | nil => simp [findPosition, accepted]
  | cons head rest ih =>
    simp only [findPosition] at absent
    split at absent
    · cases absent
    · rename_i rejected
      have tail := ih (by simpa using absent)
      simp [findPosition, List.cons_append, rejected, tail]

/-- For every table, column and requested old-field list, assume:
* Every stored row has one cell per original column.
* {name}`columnPosition` finds no original column with the added column's name.
Then projecting that name after {name}`Table.appendColumns` equals
{name}`nullExtension` of the original old-field projection. Thus every old row
contributes its physical rowid and one observed NULL. The old-field list has no
membership requirement: only its projection's rowids are used. With no rows, the
width assumption is vacuous and both projections are empty; the fresh-name
assumption remains. The proof unfolds the projections and compares each row:
freshness places the new field after the original columns, and row width makes
its selected cell the appended NULL. -/
theorem Table.project_newNullable {table : Table} {column : CatalogColumn}
    (width : ∀ row ∈ table.rows, row.values.length = table.shape.columns.length)
    (fresh : columnPosition table.shape.columns column.name = none) :
    (table.appendColumns [column]).project [column.name] =
      nullExtension (table.project fields) := by
  have absent : findPosition (fun old => normalizeIdentifier old.name == normalizeIdentifier column.name)
      table.shape.columns = none := by
    simpa [columnPosition] using fresh
  have found : columnPosition (table.shape.columns ++ [column]) column.name = some table.shape.columns.length := by
    simp [columnPosition, findPosition_append_none (item := column) absent (by simp)]
  simp only [Table.project, Table.appendColumns, nullExtension, List.map_map]
  apply List.map_congr_left
  intro row member
  simp [found, Row.appendNulls, ← width row member]

end Belay.Sqlite
