import Belay.Sqlite.Model.Queries.Evaluation.SelectSubqueryRules
import Belay.Sqlite.Model.Schema.Dispatch.SelectSubqueryRules

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every list of columns and every second list with the same affinities, in order, and every row that is
stored in the form of the second list ({name}`Row.Stored`): the row is stored in the form of the first list. In plain
words, whether a cell is in stored form depends on the affinity of its column only. Proof sketch: the column at a
position of the first list has the affinity that the second list gives at the position. -/
theorem Row.Stored.of_affinities {columns other : List CatalogColumn} {row : Row}
    (same : columns.map CatalogColumn.affinity = other.map CatalogColumn.affinity) (stored : row.Stored other) :
    row.Stored columns := by
  intro position column value atColumn atValue
  have mapped := congrArg (·[position]?) same
  simp only [List.getElem?_map, atColumn, Option.map_some] at mapped
  obtain ⟨partner, atPartner, affinity⟩ := Option.map_eq_some_iff.mp mapped.symm
  rw [← affinity]
  exact stored position partner value atPartner atValue

end Belay.Sqlite.Model
