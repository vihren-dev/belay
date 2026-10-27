import Belay.Sqlite.Model.ModelProjectionLaws

set_option doc.verso true

/-! The position of a column name after columns are appended (ADR 0017, S6). A name that an old column
has keeps its position. A name that no old column has, and that the appended column has, is found at
the old width. -/

namespace Belay.Sqlite.Model

/-- For every column list, name, position and appended columns: if the name is found at the position in
the column list, it is found there after the columns are appended. In plain words, the first matching old
column still precedes the appended columns. Proof sketch: recover the successful search and apply its
append law ({name}`findPosition_append`). -/
theorem columnPosition_append {columns : List CatalogColumn} {name : Identifier} {position : Nat}
    (found : columnPosition columns name = some position) (extra : List CatalogColumn) :
    columnPosition (columns ++ extra) name = some position := by
  obtain ⟨pair, located, equal⟩ := Option.map_eq_some_iff.mp found
  simp only [columnPosition, findPosition_append extra located, Option.map_some, equal]

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
