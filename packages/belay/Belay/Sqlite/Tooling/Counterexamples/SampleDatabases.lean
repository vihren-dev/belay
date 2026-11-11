import Belay.Sqlite.Tooling.Counterexamples.SampleValues
import Belay.Sqlite.Schema.Rows.Database

set_option doc.verso true

/-! Valid database candidates over explicit schemas. This module keeps generation separate
from proof certification, and supplies the shared bounded and targeted row distributions. -/

namespace Belay.Sqlite.Sampling

open Plausible
open Belay.Sqlite.Model (Row CatalogTable Identifier)

/-- Bundle a raw database only when its validity decision succeeds. Invalid candidates
are discarded. Use this primitive when a custom generator supplies raw database data. -/
def validated (raw : Database.Raw) : Option Database :=
  if valid : raw.Valid Profile.pinned then some ⟨raw, valid⟩ else none

/-- Build empty, nullable tables with the supplied table and column names and no declared
column affinity. An invalid schema, such as duplicate names or a table without columns,
returns none. Use a database built with {lit}`db!` for constraints, collations or indexes. -/
def schema (tables : List (String × List String)) : Option Database :=
  validated <| Belay.Sqlite.Model.Database.ofTables <| tables.map fun (name, columns) =>
    (Identifier.ofString name, { shape := { columns := columns.map fun column =>
      { name := Identifier.ofString column, declaredType := none } }, rows := [] })

/-- The stored value of the selected cell at a column position of the row with the given
index: the rowid {lit}`index + 1` for the INTEGER PRIMARY KEY alias, else the cell (NULL when it
is missing) with the column's affinity. NULL for a position outside the table. -/
def storedCell (table : CatalogTable) (index position : Nat) (cells : List Value) : Value :=
  if table.rowidAlias == some position then .integer (Int.ofNat (index + 1))
  else match table.columns[position]? with
    | some column => (cells.getD position .null).store column.affinity
    | none => .null

/-- Store supplied cells with the existing column affinities and assign distinct rowids
({name}`storedCell`). An INTEGER PRIMARY KEY alias receives that rowid. Other constraints are
checked by {name}`validated` after the complete candidate has been assembled. -/
private def row (table : CatalogTable) (index : Nat) (cells : List Value) : Row :=
  { rowid := Int.ofNat (index + 1)
    values := (List.range table.columns.length).map fun position => storedCell table index position cells }

/-- Replace each table's rows with copies of the supplied values, one value across all its
columns per row. This targets duplicate keys, case pairs and aggregate boundaries while
keeping the supplied catalog. Views and other non-table objects keep empty storage.
It returns none when constraints reject those rows. -/
def uniform (base : Database) (values : List Value) : Option Database :=
  validated { base.raw with rows := base.raw.catalog.map fun object =>
    match object.entry with
    | .table table => values.zipIdx.map fun (value, index) =>
        row table index (List.replicate table.columns.length value)
    | .index _ | .trigger _ | .view _ => [] }

/-- Ordered row-value patterns for duplicate, text-case and integer SUM boundary checks.
Each value is repeated across a table's columns by the uniform candidate constructor. -/
def boundaryRows : List (List Value) :=
  let text (value : String) := Value.text value.toUTF8.toList
  [[], [.null], [.integer 0], [.integer 1],
    [text "a", text "a"], [text "a", text "A"], [text "æ", text "Æ"],
    [.integer 4611686018427387904, .integer 4611686018427387904]]

/-- Text with its first ASCII letter in the other case, for example {lit}`'ann@x.io'` to
{lit}`'Ann@x.io'`. None for other values and for text without an ASCII letter. -/
def caseVariant : Value → Option Value
  | .text bytes =>
    let isLetter (byte : UInt8) := (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122)
    match bytes.findIdx? isLetter with
    | some position => some (.text (bytes.modify position (· ^^^ 32)))
    | none => none
  | .null | .integer _ | .real _ | .blob _ => none

/-- Rows that a supplied row of the table suggests, in this order: the row with every text in
its case variant ({name}`caseVariant`), the same row again, and for each column that allows NULL
the row with NULL in that column. The INTEGER PRIMARY KEY column is not changed. These rows
are about collations, unique keys and NOT NULL, and they satisfy most CHECK constraints that
the supplied row satisfies. -/
def rowVariants (table : CatalogTable) (values : List Value) : List (List Value) :=
  let changeable (position : Nat) := table.rowidAlias != some position
  let cased := values.zipIdx.map fun (value, position) =>
    if changeable position then (caseVariant value).getD value else value
  let nulls := table.columns.zipIdx.filterMap fun (column, position) =>
    if changeable position && !column.notNull && values[position]? != some .null then
      some (values.set position .null)
    else none
  (if cased != values then [cased] else []) ++ values :: nulls

/-- The databases with one more row in one table: a variant ({name}`rowVariants`) of the
table's first row, after the supplied rows. The new row gets the next rowid, which is also the
value of an INTEGER PRIMARY KEY column. Tables without rows give none. Rejected rows are
omitted. For example, a supplied email {lit}`'ann@x.io'` gives a database with the emails
{lit}`'ann@x.io'` and {lit}`'Ann@x.io'`. -/
def suppliedVariants (base : Database) : List Database :=
  base.raw.catalog.zipIdx.flatMap fun (object, position) =>
    match object.entry, base.raw.rows.getD position [] with
    | .table table, rows@(first :: _) =>
      let rowid := (rows.map (·.rowid)).foldl max 0 + 1
      (rowVariants table first.values).filterMap fun values =>
        let values := values.zipIdx.map fun (value, column) =>
          if table.rowidAlias == some column then .integer rowid else value
        validated { base.raw with rows := base.raw.rows.set position (rows ++ [{ rowid, values }]) }
    | .table _, [] => []
    | .view _, _ | .index _, _ | .trigger _, _ => []

/-- An upper bound of the number of {name}`suppliedVariants`: for each table with rows, its
columns and two. -/
def suppliedVariantBound (base : Database.Raw) : Nat :=
  (base.catalog.zip base.rows).foldl (fun count (object, rows) =>
    match object.entry, rows with
    | .table table, _ :: _ => count + table.columns.length + 2
    | .table _, [] => count
    | .view _, _ | .index _, _ | .trigger _, _ => count) 0

/-- Stable candidates for a supplied schema: its current rows, variants of its rows
({name}`suppliedVariants`), empty tables, singleton
NULL/zero/one rows, duplicate and ASCII/non-ASCII text pairs, an overflowing integer SUM
pair, then duplicate copies of supplied constants. Rejected rows are omitted. This order
is finite and explicit; users may prepend or replace it with their own candidates. -/
def targeted (base : Database) (constants : List Value := []) : List Database :=
  base :: suppliedVariants base ++
    (boundaryRows ++ constants.map (fun value => [value, value])).filterMap (uniform base)

/-- Select row counts and cells in catalog, row and column order, for Plausible's database
generator ({lit}`database`). Views and other non-table objects get empty storage and draw
nothing. No validity is assumed. -/
def selectCells [Monad m] (catalog : Catalog) (rowCount : m Nat) (cell : m Value) :
    m (List (List (List Value))) :=
  catalog.mapM fun object => do
    match object.entry with
    | .table table =>
      let count ← rowCount
      (List.range count).mapM fun _ => table.columns.mapM fun _ => cell
    | .index _ | .trigger _ | .view _ => pure []

/-- Assemble selected cells with the existing affinity and rowid rules. Missing cells become
NULL; views and other non-table objects retain empty storage. The result is raw data: {name}`validated` or the
kernel must still check its constraints before it can be used as a bundled database. -/
def withCells (base : Database.Raw) (cells : List (List (List Value))) : Database.Raw :=
  { base with rows := base.catalog.zipIdx.map fun (object, position) =>
    match object.entry with
    | .table table => (cells.getD position []).zipIdx.map fun (values, index) => row table index values
    | .index _ | .trigger _ | .view _ => [] }

/-- Generate up to the supplied number of rows per table, using the shared value generator
and preserving the catalog. Views and other non-table objects keep empty storage.
Failed constraints produce a generator error, so a fallback
cannot exceed the requested row bound.
The default bound is two rows; pass another bound or generator for a larger search. -/
def database (base : Database) (constants : List Value := []) (maxRows : Nat := 2) : Gen Database := do
  let cells ← selectCells base.raw.catalog
    ((·.val) <$> Gen.choose Nat 0 maxRows (Nat.zero_le _)) (value constants)
  match validated (withCells base.raw cells) with
  | some candidate => return candidate
  | none => throw (.genError "generated rows violate the supplied database constraints")

/-- The schema of Plausible's default database generator: one nullable table {lit}`t(a)`.
SQL checking supplies its inferred or explicit schemas to {name}`database` instead. -/
def defaultSchema : Database := (schema [("t", ["a"])]).getD Database.empty

end Belay.Sqlite.Sampling
