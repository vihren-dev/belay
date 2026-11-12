import Belay.Sqlite.Model.Queries.Preparation.ModelProjectionLaws

set_option doc.verso true

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

end Belay.Sqlite.Model
