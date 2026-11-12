import Belay.Sqlite.Model.Schema.Ddl.ModelLaws
import Belay.Sqlite.Model.Queries.Preparation.ModelProjectionLaws

set_option doc.verso true

/-! Constant-value extension is a structural projection fact, independent of observation contracts. -/

namespace Belay.Sqlite.Model

/-- Retain rowids and row order, replacing each row's cells with one observed
supplied value. Use {lean}`Value.null` for a nullable field without a default.
The input cells do not affect the result; an empty input gives an empty output. -/
def constantExtension (value : Value) (rows : List (Int × List (Option Value))) : List (Int × List (Option Value)) :=
  rows.map fun row => (row.1, [some value])

/-- For every table, column, value and requested old-field list, assume:
* Every stored row has one cell per original column.
* {name}`columnPosition` finds no original column with the added column's name.
Then projecting that name after {name}`Table.appendColumns` equals
{name}`constantExtension` of the original old-field projection, with the
affinity-applied value. Thus every old row contributes its physical rowid and
one observed value. The old-field list has no
membership requirement: only its projection's rowids are used. With no rows, the
width assumption is vacuous and both projections are empty; the fresh-name
assumption remains. The proof unfolds the projections and compares each row:
freshness places the new field after the original columns, and row width makes
its selected cell the appended value. -/
theorem Table.project_newColumn {table : Table} {column : CatalogColumn} (value : Value)
    (width : ∀ row ∈ table.rows, row.values.length = table.shape.columns.length)
    (fresh : columnPosition table.shape.columns column.name = none) :
    (table.appendColumns [(column, value)]).project [column.name] =
      constantExtension (Value.store column.affinity value) (table.project fields) := by
  have absent : findPosition (fun old => old.name.sameName column.name) table.shape.columns = none := by
    simpa [columnPosition] using fresh
  have found : columnPosition (table.shape.columns ++ [column]) column.name = some table.shape.columns.length := by
    simp [columnPosition, findPosition_append_none (item := column) absent (by simp)]
  simp only [Table.project, Table.appendColumns, constantExtension, List.map_map]
  apply List.map_congr_left
  intro row member
  simp [found, Row.appendValues, ← width row member]

end Belay.Sqlite.Model
