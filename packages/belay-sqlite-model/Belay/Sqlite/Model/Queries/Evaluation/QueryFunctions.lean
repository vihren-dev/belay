import Belay.Sqlite.Model.Queries.Select.QueryJoins
import Belay.Sqlite.Model.Values.Json.Each

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- The number of columns of {lit}`json_each`: {lit}`key`, {lit}`value`, {lit}`type`,
{lit}`atom`, {lit}`id`, {lit}`parent`, {lit}`fullkey`, {lit}`path`, and the hidden {lit}`json`
and {lit}`root`. -/
def eachWidth : Nat := 10

/-- The rows of the sources so far: the joined rows, the number of cells of each, and the
fault of the {lit}`json_each` calls among them. -/
structure SourceRows where
  /-- The joined rows. -/
  rows : List (List Value)
  /-- The number of cells of a joined row. -/
  width : Nat
  /-- {lean}`Fault.may` when a {lit}`json_each` call over a row so far fails, else
  {lean}`Fault.none`. -/
  fault : Fault
  /-- The enclosing query's cells, kept even when an earlier source gives no rows.
  A derived source reads these cells; an unmatched right row retains them. -/
  outer : List Value := []

/-- The rows so far joined with the rows of one table in rowid order ({name}`joinRows`): the
rows and the width of the table come from the table itself, whichever database it is from. -/
def QuerySource.joinTable (context : EvalContext) (state : SourceRows) (join : QuerySource) (table : Table) : SourceRows :=
  { state with
    rows := joinRows context state.width state.rows join table.shape.columns.length (sourceRows table) state.outer,
    width := state.width + table.shape.columns.length }

end Belay.Sqlite.Model.Resolved
