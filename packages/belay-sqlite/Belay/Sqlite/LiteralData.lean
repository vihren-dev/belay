import Belay.Sqlite.Model

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

/-- Require no NUL byte and at least one byte outside digits, signs, decimal
points, exponents and ASCII whitespace. This sufficient test prevents numeric
affinity conversion; {assert}`nonnumericText [] = false`. It is not a text decoder. -/
def nonnumericText (bytes : List UInt8) : Bool :=
  !bytes.contains 0 && bytes.any (fun byte =>
    !("0123456789+-.eE \t\r\n\x0b\x0c".toUTF8.toList.contains byte))

/-- Admit values whose modeled affinity conversion keeps them unchanged.
NULL and BLOB pass. Integers must be bounded with INTEGER, NUMERIC or BLOB
affinity. Text passes with TEXT or BLOB affinity, or with INTEGER or NUMERIC
affinity when {name}`nonnumericText` holds. REAL values do not pass.
Use {lean}`Value.null` for NULL; constraint checks remain separate. -/
def lossless (affinity : Affinity) : Value → Bool
  | .null | .blob _ => true
  | .integer value => boundedInteger value &&
      [.integer, .numeric, .blob].contains affinity
  | .text bytes => [.text, .blob].contains affinity ||
      ([.integer, .numeric].contains affinity && nonnumericText bytes)
  | .real _ => false

/-- Read the cell at a column position, or {name}`Option.none` for a missing cell,
so a malformed row cannot supply an invented value. -/
def read (row : Row) (position : Nat) : Option Value := row.values[position]?

/-- Admit NULL or a signed 64-bit integer for exact modeled comparisons.
{assert}`integerOrNull Value.null = true`; every other stored class fails. -/
def integerOrNull : Value → Bool
  | .null => true
  | .integer value => boundedInteger value
  | _ => false

/-- Require a column at the position with INTEGER, NUMERIC or BLOB affinity, and
{name}`read` at that position in every row to yield a value accepted by
{name}`integerOrNull`. With no rows only the column requirement remains. Use
this domain check before integer equality or key comparisons. -/
def comparisonReady (table : Table) (position : Nat) : Bool :=
  (table.shape.columns[position]?).any (fun column => [.integer, .numeric, .blob].contains column.affinity) &&
  table.rows.all (fun row => (read row position).any integerOrNull)

/-- For each key position, require both reads to be integers with equal values.
A missing, NULL or other cell makes the comparison false, as needed for the
admitted unique keys. An empty key compares equal vacuously;
{assert}`keyEqual [] { rowid := 0, values := [] } { rowid := 1, values := [] } = true`. -/
def keyEqual (key : List Nat) (first second : Row) : Bool :=
  key.all fun position => match read first position, read second position with
    | some (.integer a), some (.integer b) => a == b
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

/-- Require {name}`comparisonReady` for every position of every key, and
{name}`constraints` on the table. With no keys, comparison requirements are
vacuous; constraints still apply. Use this check to admit literal DML. -/
def tableReady (keys : List (List Nat)) (table : Table) : Bool :=
  keys.all (·.all (comparisonReady table)) && constraints keys table

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
{name}`lossless` on every column/value pair, a bounded rowid for every inserted
row, and an integer-or-NULL value at every key position of each row. This admits
evaluation; the inserted table's constraint truth is checked separately. -/
def insertReady (keys : List (List Nat)) (table : Table) (rows : List (List Value)) : Bool :=
  tableReady keys table &&
  rows.all (fun values => values.length == table.shape.columns.length &&
    (table.shape.columns.zip values).all (fun (column, value) => lossless column.affinity value) &&
    keys.all (·.all fun position => (values[position]?).any integerOrNull)) &&
  (inserted table rows).rows.all (fun row => boundedInteger row.rowid)

/-- Whether a row passes the optional filter: no filter, or the cell at the filter
position equals the filter value as a tagged value. Use {name}`comparisonReady`
to establish that this exact test represents SQLite's integer equality. -/
def selected (filter : Option (Nat × Value)) (row : Row) : Bool :=
  filter.all fun (position, value) => read row position == some value

/-- Set each assignment's position to its value, in order; a position beyond the
row's width changes nothing. -/
def assign (assignments : List (Nat × Value)) (row : Row) : Row :=
  assignments.foldl (fun current (position, value) => { current with values := current.values.set position value }) row

/-- Apply the assignments to every row that {name}`selected` accepts, with the
filter evaluated on the old row. Retain every rowid, other cell and the shape. -/
def updated (table : Table) (assignments : List (Nat × Value)) (filter : Option (Nat × Value)) : Table :=
  { table with rows := table.rows.map fun row => if selected filter row then assign assignments row else row }

/-- Require a filter over a {name}`comparisonReady` position with a bounded integer
value, {name}`tableReady` before the write, {name}`lossless` assignments to
existing columns, and every key position {name}`comparisonReady` after
{name}`updated`. This check does not establish the updated constraints. -/
def updateReady (keys : List (List Nat)) (table : Table) (assignments : List (Nat × Value))
    (filter : Option (Nat × Value)) : Bool :=
  filter.all (fun (position, value) => comparisonReady table position && match value with
    | .integer number => boundedInteger number
    | .null | .real _ | .text _ | .blob _ => false) &&
  tableReady keys table &&
  assignments.all (fun (position, value) =>
    (table.shape.columns[position]?).any fun column => lossless column.affinity value) &&
  keys.all (·.all (comparisonReady (updated table assignments filter)))

end LiteralData
end Belay.Sqlite
