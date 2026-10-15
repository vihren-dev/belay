import Belay.Sqlite.Model
import Belay.Sqlite.Comparison

set_option doc.verso true

/-! A closed literal-DML domain over column positions. Admission is a proof
obligation, separate from native constraint failures. Unmodeled coercions and
comparisons are never SQL errors. Writes carry the unique keys of their table as
column positions, which resolution computes from the catalog. -/
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

/-- For each key position, require both reads to be key cells that conflict
({name}`keyCellsEqual`). A missing or NULL cell makes the comparison false, so two rows
with a NULL in a key never conflict, as in SQLite. An empty key compares equal
vacuously; {assert}`keyEqual [] { rowid := 0, values := [] } { rowid := 1, values := [] } = true`. -/
def keyEqual (key : List Nat) (first second : Row) : Bool :=
  key.all fun position => match read first position, read second position with
    | some a, some b => keyCellsEqual a b
    | _, _ => false

/-- Reject each row that compares equal under {name}`keyEqual` to a later row.
Preserve duplicate NULL-containing keys because those comparisons are false.
An empty row list satisfies the check for any key. -/
def uniqueRows (key : List Nat) : List Row → Bool
  | [] => true
  | row :: rest => !(rest.any (keyEqual key row)) && uniqueRows key rest

/-- Check NOT NULL cells and the pairwise uniqueness of every given key. NOT NULL
checks inspect only zipped column/cell pairs; row width is checked separately.
A table with no rows satisfies both checks. In the admitted domain these checks
represent ABORT constraints, rather than admission restrictions. -/
def constraints (keys : List (List Nat)) (table : Table) : Bool :=
  table.rows.all (fun row => (table.shape.columns.zip row.values).all
    (fun (column, value) => !column.notNull || value != .null)) &&
  keys.all (fun key => uniqueRows key table.rows)

/-- Require {name}`constraints` on the table before a write: its NOT NULL cells and its
unique keys hold. SQLite guarantees them for every table that it stores. -/
def tableReady (keys : List (List Nat)) (table : Table) : Bool :=
  constraints keys table

/-- Return 1 for no rows, otherwise one more than the largest stored rowid,
even when that largest rowid is negative; {assert}`nextRowid [] = 1`.
SQLite's random-search branch at the maximum rowid requires separate admission. -/
def nextRowid (rows : List Row) : Int :=
  match rows with
  | [] => 1
  | first :: rest => (rest.foldl (fun largest row => max largest row.rowid) first.rowid) + 1

/-- Append one row with {name}`nextRowid` and the supplied cells. Retain columns,
keys and old row order; this function accepts any supplied value list. -/
def insertRow (table : Table) (values : List Value) : Table :=
  { table with rows := table.rows ++ [{ rowid := nextRowid table.rows, values := values }] }

/-- Append the rows in order with {name}`insertRow`, as one INSERT with several
VALUES rows does. No rows leave the table unchanged. -/
def inserted (table : Table) (rows : List (List Value)) : Table := rows.foldl insertRow table

/-- Require {name}`tableReady` before the write, one value per column in each row,
{name}`storedForm` on every column/value pair, and a bounded rowid for every inserted
row. This admits evaluation; the inserted table's constraint truth is checked
separately. -/
def insertReady (keys : List (List Nat)) (table : Table) (rows : List (List Value)) : Bool :=
  tableReady keys table &&
  rows.all (fun values => values.length == table.shape.columns.length &&
    (table.shape.columns.zip values).all (fun (column, value) => storedForm column.affinity value)) &&
  (inserted table rows).rows.all (fun row => boundedInteger row.rowid)

end LiteralData
end Belay.Sqlite
