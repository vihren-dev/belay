import Belay.Sqlite.Model.Resolution.NameTraceStatementExamples

set_option doc.verso true

/-! Examples of the name trace of the writes UPDATE, DELETE, INSERT and upsert over the catalog of
{lit}`NameTraceStatementExamples`, with the paths of the write nodes: the table at child 0, the
column list of an INSERT at child 1, the rows at child 2 and the conflict clauses at child 3. -/

namespace Belay.Sqlite.Model.NameTraceStatementExamples

/-- An UPDATE records its table at child 0, the assigned column as a target, the filter comparison and
the RETURNING column. -/
private def updateTrace : Bool :=
  let (result, trace) := run (.update (name "t") [(name "a", .numeric "5")]
    (some (.compare .eq (column "a") (.numeric "1"))) [.expression (column "b") none "b"] [])
  succeeds result &&
  sourceOf (resultAt trace [0] .tableReference) == some (.baseTable, some 0, none) &&
  (boundTo (resultAt trace [1, 0, 0] .columnTarget)).map (·.position) == some (some 0) &&
  comparedWith (resultAt trace [2] .comparisonSite) == some (some .integer, .binary) &&
  (boundTo (resultAt trace [3, 0, 0] .columnReference)).map (·.kind) == some .baseTable
#guard updateTrace

/-- An UPDATE that the model refuses keeps the occurrences up to the refusal: it assigns the column
{lit}`b` from the column {lit}`a`, which the model refuses at the value (a row-dependent key), and
the trace has the value and the target. -/
private def refusedUpdateKeepsTrace : Bool :=
  let (result, trace) := run (.update (name "t") [(name "b", column "a")] none [] [])
  refusedAt result == some [1, 0, 1] && trace.map (·.path) == [[0], [1, 0, 1], [1, 0, 0]]
#guard refusedUpdateKeepsTrace

/-- A DELETE with a filter name that no column has records the name with the two columns of the
table as candidates, and no occurrence after it. -/
private def deleteMissingColumn : Bool :=
  let trace := (run (.delete (name "t") (some (.compare .eq (column "zz") (.numeric "1"))) [] [])).2
  missingNames (resultAt trace [1, 1] .columnReference) == some [name "a", name "b"] && trace.length == 2
#guard deleteMissingColumn

/-- A DELETE from a table that the catalog lacks lists the table and the view as candidates. -/
private def deleteMissingTable : Bool :=
  let trace := (run (.delete (name "z") none [] [])).2
  missingNames (resultAt trace [0] .tableReference) == some [name "t", name "v"] && trace.length == 1
#guard deleteMissingTable

/-- An INSERT records each name of its column list as a target at child 1; a name that is no column
is missing, with the columns as candidates. A VALUES row has no columns in scope. -/
private def insertTrace : Bool :=
  let list := (run (.insert (name "t") (some [name "a", name "zz"]) [[.numeric "1", .numeric "2"]] [] none [] [])).2
  let row := (run (.insert (name "t") (some [name "a", name "b"]) [[.numeric "1", column "q"]] [] none [] [])).2
  (boundTo (resultAt list [1, 0] .columnTarget)).map (·.position) == some (some 0) &&
  missingNames (resultAt list [1, 1] .columnTarget) == some [name "a", name "b"] &&
  missingNames (resultAt row [2, 0, 1] .columnReference) == some []
#guard insertTrace

/-- An upsert records its conflict target at child 3, and in the update the qualifier
{lit}`excluded` as the proposed row of the table, with its column. -/
private def upsertTrace : Bool :=
  let proposed := Syntax.Expr.qualified (name "excluded") (name "b")
  let trace := (run (.insert (name "t") (some [name "a", name "b"]) [[.numeric "1", .numeric "2"]]
    [{ target := some [name "a"], action := .update [(name "b", proposed)] none }] none [] [])).2
  (boundTo (resultAt trace [3, 0, 0, 0] .columnTarget)).map (·.position) == some (some 0) &&
  sourceOf (resultAt trace [3, 0, 1, 0, 0, 1, 0] .qualifier) == some (.proposedRow, some 0, none) &&
  (boundTo (resultAt trace [3, 0, 1, 0, 0, 1, 1] .columnReference)).map (·.kind) == some .proposedRow
#guard upsertTrace

end Belay.Sqlite.Model.NameTraceStatementExamples
