import Belay.Sqlite.Resolution.Examples
import Belay.Sqlite.SqlExecution

set_option doc.verso true

/-! Examples of {lit}`WITHOUT ROWID` tables (ADR 0014, slice 2), checked by {lit}`#guard` when
the package builds: SQLite's prepare error for a table without a primary key, the NOT NULL
key columns, an {lit}`INTEGER PRIMARY KEY` that is no rowid alias, {lit}`rowid` as
{lit}`no such column`, and the scan order of text, composite and descending keys. The
authored corpus of {lit}`WITHOUT ROWID` tables compares the same rules with SQLite. -/

namespace Belay.Sqlite.Resolution.WithoutRowidExamples

open Belay.Sqlite Syntax Belay.Sqlite.Resolution.Examples

/-- {lit}`WITHOUT ROWID`. -/
def withoutRowid : TableOptions := { withoutRowid := true }

/-- A column with one constraint. -/
def keyed (name : Identifier) (declaredType : Option String) (constraint : ColumnConstraint) : ColumnDefinition :=
  { name, declaredType, constraints := [constraint] }

/-- The catalog of one CREATE TABLE in a schema, or the empty catalog for a restriction. -/
def tableOf (statement : Syntax.Statement) : Option CatalogTable :=
  match (catalogOf (schema [statement])).head? with
  | some { entry := .table table, .. } => some table
  | some { entry := .index _, .. } | some { entry := .trigger _, .. } | none => none

/-- {lit}`w(k TEXT PRIMARY KEY, v INTEGER) WITHOUT ROWID`. -/
def textKeyed : Syntax.Statement :=
  .createTable (name! "w") [keyed (name! "k") (some "TEXT") (.primaryKey false), column (name! "v") (some "INTEGER")]
    [] withoutRowid

-- The key columns are NOT NULL, and no column is a rowid alias.
#guard (tableOf textKeyed).map (fun table => (table.withoutRowid, table.columns.map (·.notNull), table.rowidAlias)) ==
  some (true, [true, false], none)
#guard ((tableOf (.createTable (name! "x") [keyed (name! "a") (some "INTEGER") (.primaryKey false)] [] withoutRowid)).bind
  (·.rowidAlias)) == none
-- A key that repeats a column keeps its first occurrence, as SQLite ignores the others
-- (R-03887-49864); a table with a rowid keeps them, as its key index lists them.
#guard (tableOf (.createTable (name! "r") [column (name! "a"), column (name! "b")] [.primaryKey [name! "a", name! "b", name! "a"]]
  withoutRowid)).map (·.primaryKey) == some [0, 1]
#guard (tableOf (.createTable (name! "r") [column (name! "a"), column (name! "b")] [.primaryKey [name! "a", name! "b", name! "a"]]
  {})).map (·.primaryKey) == some [0, 1, 0]
-- A table without a primary key is SQLite's prepare error.
#guard statements (schema [.createTable (name! "n") [column (name! "a")] [] withoutRowid]) ==
  [.prepareError (.expression (.primaryKeyMissing (name! "n")))]
#guard (PrepareError.expression (.primaryKeyMissing (name! "n"))).message == "PRIMARY KEY missing on table n"

/-- The schema of {lit}`textKeyed`. -/
def catalogW : Catalog := catalogOf (schema [textKeyed])

-- rowid names no column of the table: SQLite's no such column, not a model restriction.
#guard statements (migration catalogW [.select [.expression (.identifier (name! "rowid") .none) none "rowid"]
    (some { table := name! "w", alias := none }) [] none [] [] none none]) ==
  [.prepareError (.expression (.noSuchColumn (name! "rowid")))]
#guard statements (migration catalogW [.delete (name! "w") (some (.compare .eq (.identifier (name! "rowid") .none) (.numeric "1")))]) ==
  [.prepareError (.expression (.noSuchColumn (name! "rowid")))]

/-- The scan of a table with the rows of the given cells and hidden rowids in insertion order. -/
def scan (shape : CatalogTable) (rows : List (List Value)) : List (List Value) :=
  ({ shape, rows := rows.zipIdx.map fun (values, rowid) => { rowid, values } } : Table).scanRows.map (·.values)

/-- Two untyped columns {lit}`a, b`. -/
def twoColumns : List CatalogColumn := [{ name := name! "a", declaredType := none }, { name := name! "b", declaredType := none }]

/-- {lit}`(a, b, PRIMARY KEY(b, a)) WITHOUT ROWID`. -/
def composite : CatalogTable := { columns := twoColumns, primaryKey := [1, 0], withoutRowid := true }

/-- {lit}`(a PRIMARY KEY DESC) WITHOUT ROWID`. -/
def descending : CatalogTable :=
  { columns := twoColumns.take 1, primaryKey := [0], primaryKeyDescending := true, withoutRowid := true }

-- A full scan is in key order: a text key, a composite key in key order, and a descending key.
#guard (tableOf textKeyed).map (scan · [[.text [98], .integer 1], [.text [97], .integer 2]]) ==
  some [[.text [97], .integer 2], [.text [98], .integer 1]]
#guard scan composite [[.integer 2, .text [98]], [.integer 1, .text [98]], [.integer 3, .text [97]]] ==
  [[.integer 3, .text [97]], [.integer 1, .text [98]], [.integer 2, .text [98]]]
#guard scan descending [[.integer 1], [.integer 3], [.integer 2]] == [[.integer 3], [.integer 2], [.integer 1]]
-- A table with a rowid keeps rowid order.
#guard scan { columns := [{ name := name! "a", declaredType := none }] } [[.integer 2], [.integer 1]] ==
  [[.integer 2], [.integer 1]]

end Belay.Sqlite.Resolution.WithoutRowidExamples
