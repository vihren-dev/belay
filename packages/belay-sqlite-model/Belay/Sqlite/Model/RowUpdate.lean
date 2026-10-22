import Belay.Sqlite.Model.LiteralData
import Belay.Sqlite.Model.QueryEval

set_option doc.verso true

/-! The execution of UPDATE (ADR 0012, amendment 1, "Execution") and its admission
obligation. The filter and every {lit}`SET` value are evaluated on the old row; each new
value is stored with its column's affinity. -/

namespace Belay.Sqlite.Model
namespace LiteralData

/-- The affinity of the column at a position, or BLOB, which changes no value, for a
position without a column. -/
def positionAffinity (columns : List CatalogColumn) (position : Nat) : Affinity :=
  ((columns[position]?).map CatalogColumn.affinity).getD .blob

/-- Whether UPDATE selects a row: the filter condition is true on the row
({name}`Resolved.truthy`, R-58095-46013), or there is no filter (R-55869-30521). A
NULL or false condition does not select the row. -/
def selected (context : Resolved.EvalContext) (filter : Option Resolved.Expr) (row : Row) : Bool :=
  filter.all fun condition => Resolved.truthy (condition.eval context row.values)

/-- The new row of an assigned row: each assignment sets its position to the value of
its expression on the cells, stored with the column's affinity ({name}`Value.store`).
The rowid and every other cell stay; a position beyond the row's width changes nothing.
UPDATE uses the old row as the cells ({lit}`assign`); {lit}`DO UPDATE` uses the old
row followed by the proposed row. The generated columns of the new row are then computed
({name}`generatedCells`). -/
def assignFrom (context : Resolved.EvalContext) (columns : List CatalogColumn) (assignments : List (Nat × Resolved.Expr)) (cells : List Value)
    (row : Row) : Row :=
  { row with values := generatedCells columns (assignments.foldl (fun values (position, expression) =>
      values.set position (Value.store (positionAffinity columns position) (expression.eval context cells))) row.values) }

/-- The new row of a selected row of UPDATE: {name}`assignFrom` with the old row as the
cells, so each value reads the old row (R-36239-04077, R-40598-36595), and the rowid
and every other cell stay (R-40472-60438). -/
def assign (context : Resolved.EvalContext) (columns : List CatalogColumn) (assignments : List (Nat × Resolved.Expr)) (row : Row) : Row :=
  assignFrom context columns assignments row.values row

/-- The rowid of an assigned row: its rowid alias cell, when the table has an alias and the
cell is an integer, so UPDATE of the alias moves the row (slice 5b); the old rowid
otherwise. -/
def movedRowid (alias : Option Nat) (row : Row) : Row :=
  match alias.bind (row.values[·]?) with
  | some (.integer value) => { row with rowid := value }
  | some .null | some (.real _) | some (.text _) | some (.blob _) | none => row

/-- Apply the assignments to every row that {name}`selected` accepts, with the rowid of
{name}`movedRowid`. Retain the order of rows, the cells of other rows and the shape. -/
def updated (context : Resolved.EvalContext) (table : Table) (assignments : List (Nat × Resolved.Expr)) (filter : Option Resolved.Expr) : Table :=
  { table with rows := table.rows.map fun row =>
      if selected context filter row then movedRowid table.shape.rowidAlias (assign context table.shape.columns assignments row)
      else row }

/-- Whether UPDATE gives a selected row a rowid alias that SQLite refuses with
{lit}`datatype mismatch`: the table has an alias, the assignments set it, and its new
cell is not an integer (NULL included). -/
def updateMismatch (context : Resolved.EvalContext) (table : Table) (assignments : List (Nat × Resolved.Expr)) (filter : Option Resolved.Expr) :
    Bool :=
  match table.shape.rowidAlias with
  | none => false
  | some position => assignments.any (·.1 == position) && table.rows.any fun row =>
      selected context filter row && match (assign context table.shape.columns assignments row).values[position]? with
        | some (.integer _) => false
        | some .null | some (.real _) | some (.text _) | some (.blob _) | none => true

/-- Require {name}`tableReady` before the write, {name}`aliasReady`, a column at every
assigned position, and a bounded rowid for every row of the updated table ({lit}`result`,
which the execution computes: {name}`updated`). This check does not establish the updated
constraints, which {lit}`checkedWrite` checks. -/
def updateReady (keys : List UniqueKey) (table : Table) (assignments : List (Nat × Resolved.Expr))
    (result : Table) : Bool :=
  tableReady keys table && aliasReady table.shape &&
  assignments.all (fun (position, _) => (table.shape.columns[position]?).isSome) &&
  result.rows.all (fun row => boundedInteger row.rowid)

end LiteralData
end Belay.Sqlite.Model
