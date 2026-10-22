import Belay.Sqlite.Model.ExprEval
import Belay.Sqlite.Model.DatabaseFacts

set_option doc.verso true

/-! A closed literal-DML domain over column positions. Admission is a proof
obligation, separate from native constraint failures. Unmodeled coercions and
comparisons are never SQL errors. Writes carry the unique keys of their table
({name}`Belay.Sqlite.Model.UniqueKey`), which resolution computes from the catalog. -/
namespace Belay.Sqlite.Model
namespace LiteralData

/-- Check SQLite's signed 64-bit range for literals and stored comparison keys.
{assert}`boundedInteger 0 = true`; the upper bound itself is excluded. -/
def boundedInteger (value : Int) : Bool := decide (-(2 ^ 63 : Int) ≤ value ∧ value < 2 ^ 63)

/-- Whether a value is in the stored form of an affinity: {name}`Value.store` keeps it.
This is the form of every cell that SQLite stores ({name}`Row.Stored`).
{assert}`storedForm .integer (.integer 5) = true`. -/
def storedForm (affinity : Affinity) (value : Value) : Bool := Value.store affinity value == value

/-- Read the cell at a column position, or {name}`Option.none` for a missing cell,
so a malformed row cannot supply an invented value. -/
def read (row : Row) (position : Nat) : Option Value := row.values[position]?

/-- Whether two stored key cells conflict: neither is NULL, and they are equal under
SQLite's comparison with the collation ({name}`Collation.compare`, {lit}`BINARY` when none
is given), so numbers by value, TEXT by its collation, BLOB by bytes, and values of
different storage classes never. {assert}`keyCellsEqual (.text [97]) (.text [97]) = true`,
and two NULL cells never conflict. -/
def keyCellsEqual (first second : Value) (collation : Collation := .binary) : Bool :=
  first != .null && second != .null && collation.compare first second == .eq

/-- The value of a key term in a row: the cell of a column, or the value of an expression
over the row. Key expressions read no clock, so they evaluate at clock 0. A missing cell
gives {name}`Option.none`. -/
def termValue (row : Row) : KeyTerm → Option Value
  | .column position => read row position
  | .expression value => some (value.eval (.plain 0) row.values)

/-- Whether a key constrains the row: always for a key without filter, and for a partial
unique index when its filter is true for the row ({name}`Resolved.truthy`; NULL is not
true). -/
def keyApplies (key : UniqueKey) (row : Row) : Bool :=
  match key.filter with
  | none => true
  | some filter => Resolved.truthy (filter.eval (.plain 0) row.values)

/-- Whether two rows conflict on a key: the key applies to both ({name}`keyApplies`), and
for each term both values are key cells that conflict under its collation
({name}`keyCellsEqual`). A missing
or NULL value makes the comparison false, so two rows with a NULL in a key never
conflict, as in SQLite. An empty key compares equal vacuously:
{assert}`keyEqual { terms := [] } { rowid := 0, values := [] } { rowid := 1, values := [] } = true`. -/
def keyEqual (key : UniqueKey) (first second : Row) : Bool :=
  keyApplies key first && keyApplies key second &&
    key.terms.all fun term => match termValue first term.term, termValue second term.term with
      | some a, some b => keyCellsEqual a b term.collation
      | _, _ => false

/-- Reject each row that compares equal under {name}`keyEqual` to a later row.
Preserve duplicate NULL-containing keys because those comparisons are false.
An empty row list satisfies the check for any key. -/
def uniqueRows (key : UniqueKey) : List Row → Bool
  | [] => true
  | row :: rest => !(rest.any (keyEqual key row)) && uniqueRows key rest

/-- Whether a row satisfies a CHECK constraint: its condition is not false on the row, so
NULL passes (R-34109-39108). The value counts as a number, as {lit}`CAST AS NUMERIC` reads it
({name}`Resolved.truthy`, R-55435-14303). The model admits only CHECK conditions that read no clock,
so they evaluate at clock 0. -/
def checkHolds (row : Row) (check : CheckConstraint) : Bool :=
  let value := check.condition.eval (.plain 0) row.values
  value.isNull || Resolved.truthy value

/-- Whether a row satisfies every CHECK constraint of the table
({name}`CatalogTable.allChecks`); a table without CHECK constraints accepts every row. -/
def checksHold (shape : CatalogTable) (row : Row) : Bool :=
  shape.allChecks.all (checkHolds row)

/-- Whether every cell of a row fits its column's type in a {lit}`STRICT` table
({name}`StrictType.fits`); a column without a strict type takes every value. -/
def typesFit (shape : CatalogTable) (row : Row) : Bool :=
  (shape.columns.zip row.values).all fun (column, value) => column.strictType.all (·.fits value)

/-- Check that no NOT NULL column holds NULL in a row of the table. It inspects only zipped
column/cell pairs; row width is a separate fact ({lit}`Table.RowsWide`). A table with no rows
passes. -/
def notNullRows (table : Table) : Bool :=
  table.rows.all fun row => (table.shape.columns.zip row.values).all
    fun (column, value) => !column.notNull || value != .null

/-- Check that every row of the table satisfies {name}`typesFit`. A table with no rows passes. -/
def typedRows (table : Table) : Bool := table.rows.all (typesFit table.shape)

/-- Check that every row of the table satisfies {name}`checksHold`. A table with no rows passes. -/
def checkedRows (table : Table) : Bool := table.rows.all (checksHold table.shape)

/-- Check that no two rows of the table conflict on any of the given keys ({name}`uniqueRows`).
With no keys, or with at most one row, it passes. -/
def keysUnique (keys : List UniqueKey) (table : Table) : Bool := keys.all fun key => uniqueRows key table.rows

/-- Check NOT NULL cells ({name}`notNullRows`), the types of a {lit}`STRICT` table
({name}`typedRows`), the CHECK constraints of every row ({name}`checkedRows`), and the pairwise
uniqueness of every given key ({name}`keysUnique`). Row width is checked separately. A table with
no rows satisfies them all. In the admitted domain these checks represent ABORT constraints,
rather than admission restrictions. The facts of a valid database ({lit}`Database.Valid`) are
stated with the same four checks. -/
def constraints (keys : List UniqueKey) (table : Table) : Bool :=
  notNullRows table && typedRows table && checkedRows table && keysUnique keys table

/-- Require {name}`constraints` on the table before a write: its NOT NULL cells and its
unique keys hold. SQLite guarantees them for every table that it stores. -/
def tableReady (keys : List UniqueKey) (table : Table) : Bool :=
  constraints keys table

/-- Return 1 for no rows, otherwise one more than the largest stored rowid,
even when that largest rowid is negative; {assert}`nextRowid [] = 1`.
SQLite's random-search branch at the maximum rowid requires separate admission. -/
def nextRowid (rows : List Row) : Int :=
  match rows with
  | [] => 1
  | first :: rest => (rest.foldl (fun largest row => max largest row.rowid) first.rowid) + 1

/-- The rowid of a new row with the supplied cells: its rowid alias cell when the table
has an alias and the cell is an integer; otherwise {name}`nextRowid`, as for a table
without an alias or a NULL alias. -/
def newRowid (table : Table) (values : List Value) : Int :=
  match table.shape.rowidAlias.bind (values[·]?) with
  | some (.integer value) => value
  | some .null | some (.real _) | some (.text _) | some (.blob _) | none => nextRowid table.rows

/-- The cells of a row with its generated columns computed (ADR 0014, D5): each generated
cell is the value of its expression over the cells, stored with the column's affinity. One
pass per generated column settles a generated column that reads another, as resolution
admits no loop; every other cell stays. A table without generated columns keeps the cells. -/
def generatedCells (columns : List CatalogColumn) (values : List Value) : List Value :=
  let generated := columns.zipIdx.filterMap fun (column, position) =>
    column.generated.map fun how => (position, column.affinity, how.expression)
  generated.foldl (fun cells _ => generated.foldl (fun cells (position, affinity, expression) =>
    cells.set position (Value.store affinity (expression.eval (.plain 0) cells))) cells) values

/-- The cells of a new row with the rowid: the alias cell, if the table has an alias, is
the integer rowid, so a NULL alias takes the new rowid; then the generated columns are
computed ({name}`generatedCells`); other cells stay. -/
def newCells (table : Table) (values : List Value) (rowid : Int) : List Value :=
  generatedCells table.shape.columns (match table.shape.rowidAlias with
    | some position => values.set position (.integer rowid)
    | none => values)

/-- Whether the supplied cells give a rowid alias that SQLite refuses with
{lit}`datatype mismatch`: the table has an alias and its cell is neither NULL nor an
integer. Without an alias no cells do. -/
def aliasMismatch (shape : CatalogTable) (values : List Value) : Bool :=
  match shape.rowidAlias.bind (values[·]?) with
  | some (.real _) | some (.text _) | some (.blob _) => true
  | some .null | some (.integer _) | none => false

/-- Append one row with {name}`newRowid` and {name}`newCells` of the supplied cells.
Retain columns, keys and old row order; this function accepts any supplied value list. -/
def insertRow (table : Table) (values : List Value) : Table :=
  let rowid := newRowid table values
  { table with rows := table.rows ++ [{ rowid, values := newCells table values rowid }] }

/-- Append the rows in order with {name}`insertRow`, as one INSERT with several
VALUES rows does. No rows leave the table unchanged. -/
def inserted (table : Table) (rows : List (List Value)) : Table := rows.foldl insertRow table

/-- Whether the rows of the table have distinct rowids. A write whose result has two rows
with one rowid fails, as SQLite's unique constraint of a rowid alias fails: only an
explicit alias value can repeat a rowid. -/
def rowidsDistinct (table : Table) : Bool := decide (table.rows.map Row.rowid).Nodup

/-- Whether the rowid alias of a table, if it has one, is a column with INTEGER affinity:
{name}`newCells` then writes an integer in stored form. SQLite declares every alias
{lit}`INTEGER`, so every table that it stores passes. Without an alias it passes. -/
def aliasReady (shape : CatalogTable) : Bool :=
  shape.rowidAlias.all fun position => (shape.columns[position]?).any (·.affinity == .integer)

/-- Require {name}`tableReady` before the write, {name}`aliasReady`, one value per column
in each row, {name}`storedForm` on every column/value pair, and a bounded rowid for
every row of the table with the rows inserted ({lit}`result`, which the execution
computes: {name}`inserted`). This admits evaluation; the inserted table's constraint truth
is checked separately. -/
def insertReady (keys : List UniqueKey) (table : Table) (rows : List (List Value)) (result : Table) : Bool :=
  tableReady keys table && aliasReady table.shape &&
  rows.all (fun values => values.length == table.shape.columns.length &&
    (table.shape.columns.zip values).all (fun (column, value) => storedForm column.affinity value)) &&
  result.rows.all (fun row => boundedInteger row.rowid)

end LiteralData
end Belay.Sqlite.Model
