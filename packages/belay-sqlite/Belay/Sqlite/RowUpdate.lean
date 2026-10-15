import Belay.Sqlite.LiteralData
import Belay.Sqlite.QueryEval

set_option doc.verso true

/-! The execution of UPDATE (ADR 0012, amendment 1, "Execution") and its admission
obligation. The filter and every {lit}`SET` value are evaluated on the old row; each new
value is stored with its column's affinity. -/

namespace Belay.Sqlite
namespace LiteralData

/-- The affinity of the column at a position, or BLOB, which changes no value, for a
position without a column. -/
def positionAffinity (columns : List CatalogColumn) (position : Nat) : Affinity :=
  ((columns[position]?).map CatalogColumn.affinity).getD .blob

/-- Whether UPDATE selects a row: the filter condition is true on the row
({name}`Resolved.truthy`, R-58095-46013), or there is no filter (R-55869-30521). A
NULL or false condition does not select the row. -/
def selected (filter : Option Resolved.Expr) (row : Row) : Bool :=
  filter.all fun condition => Resolved.truthy (condition.eval row.values)

/-- The new row of a selected row: each assignment sets its position to the value of
its expression on the old row (R-36239-04077, R-40598-36595), stored with the
column's affinity ({name}`storeValue`). The rowid and every other cell stay
(R-40472-60438); a position beyond the row's width changes nothing. -/
def assign (columns : List CatalogColumn) (assignments : List (Nat × Resolved.Expr)) (row : Row) : Row :=
  { row with values := assignments.foldl (fun values (position, expression) =>
      values.set position (storeValue (positionAffinity columns position) (expression.eval row.values))) row.values }

/-- The rowid of an assigned row: its rowid alias cell, when the table has an alias and the
cell is an integer, so UPDATE of the alias moves the row (slice 5b); the old rowid
otherwise. -/
def movedRowid (alias : Option Nat) (row : Row) : Row :=
  match alias.bind (row.values[·]?) with
  | some (.integer value) => { row with rowid := value }
  | some .null | some (.real _) | some (.text _) | some (.blob _) | none => row

/-- Apply the assignments to every row that {name}`selected` accepts, with the rowid of
{name}`movedRowid`. Retain the order of rows, the cells of other rows and the shape. -/
def updated (table : Table) (assignments : List (Nat × Resolved.Expr)) (filter : Option Resolved.Expr) : Table :=
  { table with rows := table.rows.map fun row =>
      if selected filter row then movedRowid table.shape.rowidAlias (assign table.shape.columns assignments row)
      else row }

/-- Whether UPDATE gives a selected row a rowid alias that SQLite refuses with
{lit}`datatype mismatch`: the table has an alias, the assignments set it, and its new
cell is not an integer (NULL included). -/
def updateMismatch (table : Table) (assignments : List (Nat × Resolved.Expr)) (filter : Option Resolved.Expr) :
    Bool :=
  match table.shape.rowidAlias with
  | none => false
  | some position => assignments.any (·.1 == position) && table.rows.any fun row =>
      selected filter row && match (assign table.shape.columns assignments row).values[position]? with
        | some (.integer _) => false
        | some .null | some (.real _) | some (.text _) | some (.blob _) | none => true

/-- Require {name}`tableReady` before the write, {name}`aliasReady`, a column at every
assigned position, and a bounded rowid for every updated row. This check does not
establish the updated constraints, which {lit}`checkedWrite` checks. -/
def updateReady (keys : List (List Nat)) (table : Table) (assignments : List (Nat × Resolved.Expr))
    (filter : Option Resolved.Expr) : Bool :=
  tableReady keys table && aliasReady table.shape &&
  assignments.all (fun (position, _) => (table.shape.columns[position]?).isSome) &&
  (updated table assignments filter).rows.all (fun row => boundedInteger row.rowid)

end LiteralData
end Belay.Sqlite
