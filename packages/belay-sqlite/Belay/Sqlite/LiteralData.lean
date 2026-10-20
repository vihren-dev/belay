import Belay.Sqlite.ExprEval

set_option doc.verso true

/-! A closed literal-DML domain over column positions. Admission is a proof
obligation, separate from native constraint failures. Unmodeled coercions and
comparisons are never SQL errors. Writes carry the unique keys of their table
({name}`Belay.Sqlite.UniqueKey`), which resolution computes from the catalog. -/
namespace Belay.Sqlite
namespace LiteralData

/-- Check SQLite's signed 64-bit range for literals and stored comparison keys.
{assert}`boundedInteger 0 = true`; the upper bound itself is excluded. -/
def boundedInteger (value : Int) : Bool := decide (-(2 ^ 63 : Int) ≤ value ∧ value < 2 ^ 63)

/-- Whether a value is in the stored form of an affinity: {name}`storeValue` keeps it.
This is the form of every cell that SQLite stores ({name}`Row.Stored`).
{assert}`storedForm .integer (.integer 5) = true`. -/
def storedForm (affinity : Affinity) (value : Value) : Bool := storeValue affinity value == value

/-- Read the cell at a column position, or {name}`Option.none` for a missing cell,
so a malformed row cannot supply an invented value. -/
def read (row : Row) (position : Nat) : Option Value := row.values[position]?

/-- Whether two stored key cells conflict: neither is NULL, and they are equal under
SQLite's comparison with the BINARY collation ({name}`compareValues`), so numbers by
value, TEXT and BLOB by bytes, and values of different storage classes never.
{assert}`keyCellsEqual (.text [97]) (.text [97]) = true`, and two NULL cells never
conflict. -/
def keyCellsEqual (first second : Value) : Bool :=
  first != .null && second != .null && compareValues first second == .eq

/-- The value of a key term in a row: the cell of a column, or the value of an expression
over the row. Key expressions read no clock, so they evaluate at clock 0. A missing cell
gives {name}`Option.none`. -/
def termValue (row : Row) : KeyTerm → Option Value
  | .column position => read row position
  | .expression value => some (value.eval 0 row.values)

/-- Whether a key constrains the row: always for a key without filter, and for a partial
unique index when its filter is true for the row ({name}`Resolved.truthy`; NULL is not
true). -/
def keyApplies (key : UniqueKey) (row : Row) : Bool :=
  match key.filter with
  | none => true
  | some filter => Resolved.truthy (filter.eval 0 row.values)

/-- Whether two rows conflict on a key: the key applies to both ({name}`keyApplies`), and
for each term both values are key cells that conflict ({name}`keyCellsEqual`). A missing
or NULL value makes the comparison false, so two rows with a NULL in a key never
conflict, as in SQLite. An empty key compares equal vacuously:
{assert}`keyEqual { terms := [] } { rowid := 0, values := [] } { rowid := 1, values := [] } = true`. -/
def keyEqual (key : UniqueKey) (first second : Row) : Bool :=
  keyApplies key first && keyApplies key second &&
    key.terms.all fun term => match termValue first term, termValue second term with
      | some a, some b => keyCellsEqual a b
      | _, _ => false

/-- Reject each row that compares equal under {name}`keyEqual` to a later row.
Preserve duplicate NULL-containing keys because those comparisons are false.
An empty row list satisfies the check for any key. -/
def uniqueRows (key : UniqueKey) : List Row → Bool
  | [] => true
  | row :: rest => !(rest.any (keyEqual key row)) && uniqueRows key rest

/-- Check NOT NULL cells and the pairwise uniqueness of every given key. NOT NULL
checks inspect only zipped column/cell pairs; row width is checked separately.
A table with no rows satisfies both checks. In the admitted domain these checks
represent ABORT constraints, rather than admission restrictions. -/
def constraints (keys : List UniqueKey) (table : Table) : Bool :=
  table.rows.all (fun row => (table.shape.columns.zip row.values).all
    (fun (column, value) => !column.notNull || value != .null)) &&
  keys.all (fun key => uniqueRows key table.rows)

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

/-- The cells of a new row with the rowid: the alias cell, if the table has an alias, is
the integer rowid, so a NULL alias takes the new rowid; other cells stay. -/
def newCells (table : Table) (values : List Value) (rowid : Int) : List Value :=
  match table.shape.rowidAlias with
  | some position => values.set position (.integer rowid)
  | none => values

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
end Belay.Sqlite
