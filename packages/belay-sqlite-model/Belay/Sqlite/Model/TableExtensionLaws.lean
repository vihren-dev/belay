import Belay.Sqlite.Model.PreservationLaws

set_option doc.verso true

/-! Row-level facts of a table extension ({name}`Belay.Sqlite.Model.TableExtends`): the extension keeps the
order of the rowids and the old values of each row. They hold for arbitrary initial rows,
including duplicate application values. -/

namespace Belay.Sqlite.Model

/-- For every table extension, the ordered list of after rowids equals the
before list. The proof unfolds value extension; duplicate rowids are not excluded
by this statement. -/
theorem TableExtends.rowids (extension : TableExtends before after) :
    after.rows.map Row.rowid = before.rows.map Row.rowid := by
  obtain ⟨columns, rfl⟩ := extension
  simp [Table.appendColumns, Row.appendValues, List.map_map, Function.comp_def]

/-- For every table extension whose before rows each have the before column
width, taking that many values from every after row gives the exact ordered
before value lists. With no rows the claim is vacuous. The proof unfolds value
extension and uses the width assumption for each row. -/
theorem TableExtends.oldValues (extension : TableExtends before after)
    (width : ∀ row ∈ before.rows, row.values.length = before.shape.columns.length) :
    after.rows.map (fun row => row.values.take before.shape.columns.length) =
      before.rows.map Row.values := by
  obtain ⟨columns, rfl⟩ := extension
  simp only [Table.appendColumns, List.map_map]
  apply List.map_congr_left
  intro row member
  simp [Row.appendValues, ← width row member]

end Belay.Sqlite.Model
