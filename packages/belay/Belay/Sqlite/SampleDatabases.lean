import Belay.Sqlite.SampleValues
import Belay.Sqlite.Database

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

/-- Store supplied cells with the existing column affinities and assign distinct rowids.
An INTEGER PRIMARY KEY alias receives that rowid. Other constraints are checked by
{name}`validated` after the complete candidate has been assembled. -/
private def row (table : CatalogTable) (index : Nat) (cells : List Value) : Row :=
  let rowid := Int.ofNat (index + 1)
  { rowid, values := table.columns.zipIdx.map fun (column, position) =>
      if table.rowidAlias == some position then .integer rowid
      else (cells.getD position .null).store column.affinity }

/-- Replace each table's rows with copies of the supplied values, one value across all its
columns per row. This targets duplicate keys, case pairs and aggregate boundaries while
keeping the supplied catalog. It returns none when constraints reject those rows. -/
def uniform (base : Database) (values : List Value) : Option Database :=
  validated { base.raw with rows := base.raw.catalog.map fun object =>
    match object.entry with
    | .table table => values.zipIdx.map fun (value, index) =>
        row table index (List.replicate table.columns.length value)
    | .index _ | .trigger _ => [] }

/-- Ordered row-value patterns for duplicate, text-case and integer SUM boundary checks.
Each value is repeated across a table's columns by the uniform candidate constructor. -/
def boundaryRows : List (List Value) :=
  let text (value : String) := Value.text value.toUTF8.toList
  [[], [.null], [.integer 0], [.integer 1],
    [text "a", text "a"], [text "a", text "A"], [text "æ", text "Æ"],
    [.integer 4611686018427387904, .integer 4611686018427387904]]

/-- Stable candidates for a supplied schema: its current rows, empty tables, singleton
NULL/zero/one rows, duplicate and ASCII/non-ASCII text pairs, an overflowing integer SUM
pair, then duplicate copies of supplied constants. Rejected rows are omitted. This order
is finite and explicit; users may prepend or replace it with their own candidates. -/
def targeted (base : Database) (constants : List Value := []) : List Database :=
  base :: (boundaryRows ++ constants.map (fun value => [value, value])).filterMap (uniform base)

/-- Select row counts and cells in catalog, row and column order. Non-table objects get
empty storage. Ordinary Plausible sampling and cooperative checking share this traversal;
the optional resource action runs before each object and row, including zero-column rows.
The incremental row loop does not allocate a range before the first check. No validity is assumed. -/
def selectCells [Monad m] (catalog : Catalog) (rowCount : m Nat) (cell : m Value)
    (check : m Unit := pure ()) : m (List (List (List Value))) :=
  catalog.mapM fun object => do
    check
    match object.entry with
    | .table table =>
      let count ← rowCount
      let mut rows := []
      for _ in [:count] do
        check
        rows := (← table.columns.mapM fun _ => cell) :: rows
      return rows.reverse
    | .index _ | .trigger _ => pure []

/-- Assemble selected cells with the existing affinity and rowid rules. Missing cells become
NULL and non-table storage remains empty. The result is raw data: {name}`validated` or the
kernel must still check its constraints before it can be used as a bundled database. -/
def withCells (base : Database.Raw) (cells : List (List (List Value))) : Database.Raw :=
  { base with rows := base.catalog.zipIdx.map fun (object, position) =>
    match object.entry with
    | .table table => (cells.getD position []).zipIdx.map fun (values, index) => row table index values
    | .index _ | .trigger _ => [] }

/-- Generate up to the supplied number of rows per table, using the shared value generator
and preserving the catalog. Failed constraints produce a generator error, so a fallback
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
