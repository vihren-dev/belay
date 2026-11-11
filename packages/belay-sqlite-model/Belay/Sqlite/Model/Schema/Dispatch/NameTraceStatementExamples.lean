import Belay.Sqlite.Model.Schema.Dispatch.CommonTableResolutionExamples
import Belay.Sqlite.Model.Queries.Preparation.NameTraceStatementExamples

set_option doc.verso true

/-! Examples of the name trace of whole statements, from {lit}`resolveStatementTraced`: SELECT, UPDATE
with RETURNING, DELETE, INSERT, upsert, a stored view and a {lit}`WITH` definition. The catalog has the
table {lit}`t(a INTEGER PRIMARY KEY, b TEXT UNIQUE)` at position 0 and the view {lit}`v` (a query of
{lit}`t`) at position 1. Each check reads occurrences by path and role. -/

namespace Belay.Sqlite.Model.NameTraceStatementExamples

/-- The traced resolution of a statement over {lean}`catalog`. -/
def run (statement : Syntax.Statement) :=
  resolveStatementTraced { profile := Profile.pinned, mode := .execution } { catalog } statement

/-- A SELECT binds a result column to the primary key, a filter column to the UNIQUE column, and
records the comparison with the affinity of {lit}`b` (text). -/
private def selectTrace : Bool :=
  let trace := (run (select (column "a") "t" (some filterOnB))).2
  sourceOf (resultAt trace [1, 0] .tableReference) == some (.baseTable, some 0, none) &&
  (boundTo (resultAt trace [0, 0, 0] .columnReference)).map (·.constraints.map (·.primaryKey)) == some (some true) &&
  (boundTo (resultAt trace [3, 1] .columnReference)).map (·.constraints.map (·.unique)) == some (some true) &&
  comparedWith (resultAt trace [3] .comparisonSite) == some (some .text, .binary)
#guard selectTrace

/-- A SELECT over a view records the view as a source with its catalog position and its query, the
names inside the view body at the path of the use (not exact), and the result column bound to the view. -/
private def viewTrace : Bool :=
  let trace := (run (select (column "a") "v")).2
  sourceOf (resultAt trace [1, 0] .tableReference) == some (.storedView, some 1, some 0) &&
  (trace.filter fun occurrence => !occurrence.exact).all (·.path == [1]) &&
  (trace.filter fun occurrence => !occurrence.exact).length == 2 &&
  (boundTo (resultAt trace [0, 0, 0] .columnReference)).map (·.kind) == some .storedView
#guard viewTrace

/-- The definition of a {lit}`WITH` clause is declared at child 0 of its subquery 12, the name of the
definition reads as a common table, and the result column binds to it. -/
private def definitionTrace : Bool :=
  let trace := (run (select (column "a") "c" none
    [{ query "t" with commonTable := some { name := name "c", columns := none } }])).2
  (resultAt trace [8, 0, 12, 0] .aliasDeclaration) == some .declares &&
  sourceOf (resultAt trace [1, 0] .tableReference) == some (.commonTable, none, some 0) &&
  sourceOf (resultAt trace [8, 0, 1, 0] .tableReference) == some (.baseTable, some 0, none) &&
  (boundTo (resultAt trace [0, 0, 0] .columnReference)).map (·.kind) == some .commonTable
#guard definitionTrace

/-- A table alias hides the name of the table: the qualifier {lit}`t` names the view {lit}`v` that has
the alias {lit}`t`, and the table {lit}`t` of the catalog is not in the trace for that qualifier. -/
private def aliasHidesTable : Bool :=
  let trace := (run (.select [.expression (.qualified (name "t") (name "a")) none "r"]
    (some { table := name "v", alias := some (name "t") }) [] none [] [] none none)).2
  sourceOf (resultAt trace [0, 0, 0, 0] .qualifier) == some (.storedView, some 1, some 0) &&
  (boundTo (resultAt trace [0, 0, 0, 1] .columnReference)).map (·.kind) == some .storedView &&
  resultAt trace [1, 1] .aliasDeclaration == some .declares
#guard aliasHidesTable

/-- A subquery that names a column of the enclosing query binds it at depth 1. -/
private def correlatedName : Bool :=
  let inner := query "v" (some (.compare .eq (.qualified (name "v") (name "a")) (.qualified (name "t") (name "a"))))
  let trace := (run (select (column "a") "t" (some (.exists 0)) [inner])).2
  (boundTo (resultAt trace [8, 0, 3, 2, 1] .columnReference)).map (fun bound => (bound.kind, bound.depth)) ==
    some (.baseTable, 1) &&
  (boundTo (resultAt trace [8, 0, 3, 1, 1] .columnReference)).map (fun bound => (bound.kind, bound.depth)) ==
    some (.storedView, 0)
#guard correlatedName

/-- A name that both joined sources have is ambiguous, but after a NATURAL join it names the merged
column, which binds to the left table. -/
private def naturalJoinMergesColumn : Bool :=
  isAmbiguous (resultAt (run (joinWith [])).2 [0, 0, 0] .columnReference) &&
  (boundTo (resultAt (run (joinWith ["NATURAL"])).2 [0, 0, 0] .columnReference)).map (·.kind) == some .baseTable
#guard naturalJoinMergesColumn

/-- The comparison of a column with a literal records the affinity that the operand gives: a CAST
operand has the affinity of its type name, a unary plus has none, and a COLLATE operand sets the
collation of the comparison. -/
private def comparisonOperands : Bool :=
  let compared := fun (operand : Syntax.Expr) =>
    comparedWith (resultAt (run (select (.compare .eq operand (.numeric "1")) "t")).2 [0, 0, 0] .comparisonSite)
  compared (.cast (column "a") "TEXT") == some (some .text, .binary) &&
  compared (.positive (column "a")) == some (none, .binary) &&
  compared (.collate (column "b") (name "NOCASE")) == some (some .text, .nocase)
#guard comparisonOperands

/-- A SELECT with {lit}`b BETWEEN 0 AND 2` keeps the two comparisons of the bounds, which have one path
({lit}`[0, 0, 0]`), with the affinity of the column. -/
private def betweenKeepsBothBounds : Bool :=
  let trace := (run (select (.between (column "b") (.numeric "0") (.numeric "2") false) "t")).2
  (trace.filter fun occurrence => occurrence.role == .comparisonSite).map
    (fun occurrence => (occurrence.path, occurrence.result.comparisonForm)) ==
    [([0, 0, 0], some ComparisonForm.betweenLow), ([0, 0, 0], some ComparisonForm.betweenHigh)]
#guard betweenKeepsBothBounds

end Belay.Sqlite.Model.NameTraceStatementExamples
