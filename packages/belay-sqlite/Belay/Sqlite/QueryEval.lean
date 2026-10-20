import Belay.Sqlite.ExprEval
import Belay.Sqlite.Comparison
import Belay.Sqlite.Summation
import Belay.Sqlite.Json.JsonApply
import Belay.Sqlite.Date.Functions

set_option doc.verso true

/-! The Expressions and Queries levels of ADR 0012, slice 1 and amendments 2 and 3: the
value of an expression over one row, and the result rows of a query over its source
rows ({lit}`QueryJoins.lean` joins the tables into the source rows; a joined row is the
concatenation of the cells of its tables). The steps follow the ADR in order: the
{lit}`WHERE` filter, the groups, the result columns, a stable sort by the
{lit}`ORDER BY` terms, and the {lit}`OFFSET` and {lit}`LIMIT` window. -/

namespace Belay.Sqlite.Resolved

/-- The first value of a list that no later value improves on, ignoring NULL; NULL
when every value is NULL. A tie keeps the earlier value, as SQLite's {lit}`min()` and
{lit}`max()` do. -/
def extremum (better : Value → Value → Bool) (values : List Value) : Value :=
  (values.filter (!·.isNull)).foldl (fun best value => if best.isNull || better value best then value else best) .null

/-- The value of an aggregate over the rows of one group. The JSON aggregates read whether
each value has the JSON subtype ({name}`Expr.givesJson`). -/
def Aggregate.eval (clock : Int) (rows : List (List Value)) : Aggregate → Value
  | .countRows => .integer rows.length
  | .count operand => .integer (rows.filter fun row => !(operand.eval clock row).isNull).length
  | .min operand collation => extremum (fun a b => collation.compare a b == .lt) (rows.map (operand.eval clock))
  | .max operand collation => extremum (fun a b => collation.compare a b == .gt) (rows.map (operand.eval clock))
  | .sum operand => ((sumOf (rows.map (operand.eval clock))).sumValue).getD .null
  | .avg operand => (sumOf (rows.map (operand.eval clock))).averageValue
  | .jsonGroupArray operand binary =>
    Json.groupOutput binary (Json.groupArray (rows.map fun row => (operand.eval clock row, operand.givesJson clock row)))
  | .jsonGroupObject label value binary => Json.groupOutput binary
    (Json.groupObject (rows.map fun row => (label.eval clock row, value.eval clock row, value.givesJson clock row)))

/-- Whether an aggregate fails over the rows of one group: {lit}`SUM` with an integer
overflow that no later REAL input cleared. Every other aggregate never fails. -/
def Aggregate.fails (clock : Int) (rows : List (List Value)) : Aggregate → Bool
  | .sum operand => ((sumOf (rows.map (operand.eval clock))).sumValue).isNone
  | .countRows | .count _ | .min .. | .max .. | .avg _ | .jsonGroupArray .. | .jsonGroupObject .. => false

/-- The groups of rows by the values of the grouping terms, in the order in which
each group first appears. Two rows are in one group when each term's values compare
as equal under the term's collation. -/
def groups (clock : Int) (terms : List (Expr × Collation)) (rows : List (List Value)) : List (List (List Value)) :=
  let key := fun row => terms.map fun (term, _) => term.eval clock row
  let same := fun first second => ((terms.map (·.2)).zip ((key first).zip (key second))).all
    fun (collation, a, b) => collation.compare a b == .eq
  (rows.foldl (fun found row => match found.findIdx? (fun group => group.head?.any (same row)) with
    | some index => found.modify index (· ++ [row])
    | none => found ++ [[row]]) [])

/-- One {lit}`ORDER BY` comparison under a collation: ascending, or descending when
{lit}`descending` is true. NULL is first in ascending order (R-12881-55998). -/
def compareTerm (descending : Bool) (collation : Collation) (a b : Value) : Ordering :=
  if descending then collation.compare b a else collation.compare a b

/-- The comparison of two lists of sort values, term by term, with one direction and one
collation per term; the first term that differs decides. A missing value reads as NULL. -/
def compareSort : List (Bool × Collation) → List Value → List Value → Ordering
  | [], _, _ => .eq
  | (descending, collation) :: orders, a, b =>
    (compareTerm descending collation (a.headD .null) (b.headD .null)).then (compareSort orders a.tail b.tail)

/-- Insert an item into a list after every leading item that is at most the new
item by {lit}`le`. In a sorted list, the item goes after its equals, which keeps a
sort stable. -/
def insertStable (le : α → α → Bool) (item : α) : List α → List α
  | [] => [item]
  | head :: tail => if le head item then head :: insertStable le item tail else item :: head :: tail

/-- A stable sort by {lit}`le`: each item, in list order, is inserted after its
equals. Unlike {lit}`List.mergeSort`, it uses only structural recursion, so the
kernel can evaluate it in the proofs of conformance cases. -/
def stableSort (le : α → α → Bool) (items : List α) : List α :=
  items.foldl (fun sorted item => insertStable le item sorted) []

/-- A result row with its sort values. -/
abbrev Record := List Value × List Value

/-- The groups of an aggregate query: all rows as one group without {lit}`GROUP BY`,
also when there are none; else the groups of the grouping terms. -/
def queryGroups (clock : Int) (query : Query) (rows : List (List Value)) : List (List (List Value)) :=
  if query.groupBy.isEmpty then [rows] else groups clock query.groupBy rows

/-- The result rows and sort values of a query, one per source row, or one per group
of an aggregate query. -/
def records (clock : Int) (query : Query) (rows : List (List Value)) : List Record :=
  let sortValues := fun (output : List Value) (source : List Value) =>
    query.orderBy.map fun term => match term.key with
      | .expression expression => expression.eval clock source
      | .output index => output.getD index .null
  if query.aggregate then
    (queryGroups clock query rows).map fun group =>
      let output := query.columns.map fun
        | .scalar expression => expression.eval clock (group.headD [])
        | .aggregate aggregate => aggregate.eval clock group
      (output, sortValues output (group.headD []))
  else
    rows.map fun row =>
      let output := query.columns.map fun
        | .scalar expression => expression.eval clock row
        | .aggregate aggregate => aggregate.eval clock [row]
      (output, sortValues output row)

/-- The primary-key cells of a row, in key order; a missing cell reads as NULL. -/
def _root_.Belay.Sqlite.Table.keyCells (table : Table) (row : Row) : List Value :=
  table.shape.primaryKey.map fun position => row.values.getD position .null

/-- The rows of the table in the order of a full scan: rowid order, or for a
{lit}`WITHOUT ROWID` table primary-key order ({name}`compareSort` of {name}`Belay.Sqlite.Table.keyCells`),
descending for {lit}`PRIMARY KEY DESC`, under the key columns' collations, as SQLite's key
b-tree gives them (ADR 0014, D4). -/
def _root_.Belay.Sqlite.Table.scanRows (table : Table) : List Row :=
  if table.shape.withoutRowid then
    let directions := table.shape.primaryKey.map fun position =>
      (table.shape.primaryKeyDescending, (table.shape.columns[position]?.map (·.collation)).getD .binary)
    stableSort (fun a b => (compareSort directions (table.keyCells a) (table.keyCells b)).isLE) table.rows
  else stableSort (fun a b => decide (a.rowid ≤ b.rowid)) table.rows

/-- The rows of the table in scan order ({name}`Belay.Sqlite.Table.scanRows`), as the source of a query. -/
def sourceRows (table : Table) : List (List Value) := table.scanRows.map Row.values

/-- The rows that the {lit}`WHERE` condition keeps: those where it is true. -/
def filtered (clock : Int) (query : Query) (rows : List (List Value)) : List (List Value) :=
  rows.filter fun row => query.filter.all fun condition => truthy (condition.eval clock row)

/-- The result rows of a query over its source rows ({lit}`Query.source`): filter,
groups and columns, a stable sort by the {lit}`ORDER BY` terms, then the window.
{lit}`Query.run` gives them with the fault of the query. -/
def Query.results (clock : Int) (query : Query) (rows : List (List Value)) : List (List Value) :=
  let directions := query.orderBy.map fun term => (term.descending, term.collation)
  let sorted := stableSort (fun a b => (compareSort directions a.2 b.2).isLE)
    (records clock query (filtered clock query rows))
  let window := sorted.drop query.offset
  (match query.limit with | some limit => window.take limit | none => window).map Prod.fst

end Belay.Sqlite.Resolved
