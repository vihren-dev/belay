import Belay.Sqlite.Model
import Belay.Sqlite.Resolution.QueryForm

set_option doc.verso true

/-! The Expressions and Queries levels of ADR 0012, slice 1: the value of an
expression over one row, and the result rows of a single-table query. The steps
follow the ADR in order: the rows in rowid order, the {lit}`WHERE` filter, the
groups, the result columns, a stable sort by the {lit}`ORDER BY` terms, and the
{lit}`OFFSET` and {lit}`LIMIT` window. -/

namespace Belay.Sqlite.Resolved

/-- Whether a value is true as a condition: a number that is not zero. -/
def truthy : Value → Bool
  | .integer value => value != 0
  | .real bits => (realScaled bits).any (· != 0)
  | .null | .text _ | .blob _ => false

/-- Whether a value is false as a condition: not NULL and not true. -/
def falsy (value : Value) : Bool := !value.isNull && !truthy value

/-- The value of an expression over the cells of one row, in column order. A column
past the end of the row reads as NULL. {lit}`AND` is false when an operand is false,
else NULL when an operand is NULL, else true; {lit}`OR` is the dual; {lit}`NOT`
keeps NULL. -/
def Expr.eval (row : List Value) : Expr → Value
  | .column position => row.getD position .null
  | .literal value => value
  | .compare operator left right => operator.apply (left.eval row) (right.eval row)
  | .and left right =>
    let (a, b) := (left.eval row, right.eval row)
    if falsy a || falsy b then truth false else if a.isNull || b.isNull then .null else truth true
  | .or left right =>
    let (a, b) := (left.eval row, right.eval row)
    if truthy a || truthy b then truth true else if a.isNull || b.isNull then .null else truth false
  | .not operand =>
    let value := operand.eval row
    if value.isNull then .null else truth (!truthy value)
  | .isNull operand negated => truth ((operand.eval row).isNull != negated)

/-- The first value of a list that no later value improves on, ignoring NULL; NULL
when every value is NULL. A tie keeps the earlier value, as SQLite's {lit}`min()` and
{lit}`max()` do. -/
def extremum (better : Value → Value → Bool) (values : List Value) : Value :=
  (values.filter (!·.isNull)).foldl (fun best value => if best.isNull || better value best then value else best) .null

/-- The value of an aggregate over the rows of one group. -/
def Aggregate.eval (rows : List (List Value)) : Aggregate → Value
  | .countRows => .integer rows.length
  | .count operand => .integer (rows.filter fun row => !(operand.eval row).isNull).length
  | .min operand => extremum (fun a b => compareValues a b == .lt) (rows.map operand.eval)
  | .max operand => extremum (fun a b => compareValues a b == .gt) (rows.map operand.eval)

/-- The groups of rows by the values of the grouping terms, in the order in which
each group first appears. Two rows are in one group when each term's values compare
as equal. -/
def groups (terms : List Expr) (rows : List (List Value)) : List (List (List Value)) :=
  let key := fun row => terms.map (·.eval row)
  let same := fun first second => (List.zip (key first) (key second)).all fun (a, b) => compareValues a b == .eq
  (rows.foldl (fun found row => match found.findIdx? (fun group => group.head?.any (same row)) with
    | some index => found.modify index (· ++ [row])
    | none => found ++ [[row]]) [])

/-- One {lit}`ORDER BY` comparison: ascending, or descending when {lit}`descending`
is true. NULL is first in ascending order (R-12881-55998). -/
def compareTerm (descending : Bool) (a b : Value) : Ordering :=
  if descending then compareValues b a else compareValues a b

/-- The comparison of two lists of sort values, term by term, with one direction
per term; the first term that differs decides. A missing value reads as NULL. -/
def compareSort : List Bool → List Value → List Value → Ordering
  | [], _, _ => .eq
  | descending :: directions, a, b =>
    (compareTerm descending (a.headD .null) (b.headD .null)).then (compareSort directions a.tail b.tail)

/-- A result row with its sort values. -/
abbrev Record := List Value × List Value

/-- The result rows and sort values of a query, one per source row, or one per group
of an aggregate query. -/
def records (query : Query) (rows : List (List Value)) : List Record :=
  let sortValues := fun (output : List Value) (source : List Value) =>
    query.orderBy.map fun (key, _) => match key with
      | .expression expression => expression.eval source
      | .output index => output.getD index .null
  if query.aggregate then
    let grouped := if query.groupBy.isEmpty then [rows] else groups query.groupBy rows
    grouped.map fun group =>
      let output := query.columns.map fun
        | .scalar expression => expression.eval (group.headD [])
        | .aggregate aggregate => aggregate.eval group
      (output, sortValues output (group.headD []))
  else
    rows.map fun row =>
      let output := query.columns.map fun
        | .scalar expression => expression.eval row
        | .aggregate aggregate => aggregate.eval [row]
      (output, sortValues output row)

/-- The rows of the table in rowid order, as the source of a query. -/
def sourceRows (table : Table) : List (List Value) :=
  (table.rows.mergeSort fun a b => decide (a.rowid ≤ b.rowid)).map Row.values

/-- The rows that the {lit}`WHERE` condition keeps: those where it is true. -/
def filtered (query : Query) (rows : List (List Value)) : List (List Value) :=
  rows.filter fun row => query.filter.all fun condition => truthy (condition.eval row)

/-- The result rows of a query over a table: filter, groups and columns, a stable
sort by the {lit}`ORDER BY` terms, then the window. -/
def Query.run (query : Query) (table : Table) : List (List Value) :=
  let directions := query.orderBy.map Prod.snd
  let sorted := (records query (filtered query (sourceRows table))).mergeSort fun a b =>
    (compareSort directions a.2 b.2).isLE
  let window := sorted.drop query.offset
  (match query.limit with | some limit => window.take limit | none => window).map Prod.fst

end Belay.Sqlite.Resolved
