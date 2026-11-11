import Belay.Sqlite.Model.Queries.Select.Defaults
import Belay.Sqlite.Model.Schema.Columns.Defaults
import Belay.Sqlite.Model.Queries.Preparation.Assignments

set_option doc.verso true

/-! The cells of a resolved INSERT row (ADR 0012, slices 3a and 6e2; ADR 0013, D6). A
{lit}`VALUES` item or an omitted column gets its value at resolution, stored with the
column's affinity; one whose value reads the statement's clock, such as
{lit}`CURRENT_TIMESTAMP` or {lit}`DEFAULT CURRENT_TIMESTAMP`, stays an expression
({lit}`Resolved.Cell.expression`), which the execution evaluates at the statement's clock
value and stores. -/

namespace Belay.Sqlite.Model

/-- The cell of an omitted column: its default ({name}`defaultValue`) stored with the
column's affinity; or the time keyword of a default that is one, such as
{lit}`DEFAULT CURRENT_TIMESTAMP`. -/
def omittedCell (column : CatalogColumn) : Except ValueIssue Resolved.Cell :=
  match column.defaultValue with
  | some { form := .clock keyword, .. } => .ok (.expression (.now keyword))
  | some { form := .literal .., .. } | none => (defaultValue column).map fun value => .value (Value.store column.affinity value)

/-- A written cell stored with a column's affinity: a value is stored ({name}`Value.store`);
an expression stays as it is, and the execution stores its value. -/
def Resolved.Cell.stored (affinity : Affinity) : Resolved.Cell → Resolved.Cell
  | .value written => .value (Value.store affinity written)
  | .expression term => .expression term

/-- One full row of cells in table order: the written cell of a named column stored with
the column's affinity ({name}`Resolved.Cell.stored`), or the cell of an omitted column
({name}`omittedCell`). -/
def fullCells (columns : List CatalogColumn) (positions : List Nat) (row : List Resolved.Cell) :
    Except ValueIssue (List Resolved.Cell) :=
  resolveAll (fun position column => match positions.idxOf? position with
    | some written => .ok ((row[written]?.getD (.value .null)).stored column.affinity)
    | none => omittedCell column) columns

end Belay.Sqlite.Model
