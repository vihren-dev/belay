import Belay.Sqlite.Model.Schema.Columns.ModelProjectionLaws

set_option doc.verso true

/-! The position of a column name after columns are appended (ADR 0017, S6). A name that an old column
has keeps its position. A name that no old column has, and that the appended column has, is found at
the old width. -/

namespace Belay.Sqlite.Model

/-- For every column list, name and appended column: if no old column has the name and the appended
column has it ({name}`Identifier.sameName`), the name is found at the old width after the column is
appended. Proof sketch: the absent prefix and the matching final name satisfy the first-match search
({name}`findPosition_append_none`). -/
theorem columnPosition_append_new {columns : List CatalogColumn} {name : Identifier} {column : CatalogColumn}
    (fresh : columnPosition columns name = none) (named : column.name.sameName name = true) :
    columnPosition (columns ++ [column]) name = some columns.length := by
  have absent : findPosition (fun column => column.name.sameName name) columns = none := by
    simpa only [columnPosition, Option.map_eq_none_iff] using fresh
  simp [columnPosition, findPosition_append_none (item := column) absent named]

end Belay.Sqlite.Model
