import VerifierConformance.Trace

/-! Native SQLite observations of tables and their catalog metadata, and their
comparison with the model's catalog and tables. The frontend reads the metadata
from {lit}`sqlite_schema`, {lit}`PRAGMA table_xinfo`, {lit}`PRAGMA index_list` and
{lit}`PRAGMA index_xinfo`; this comparison is how the conformance suite checks the
catalog that resolution computes. -/

namespace Belay.Sqlite.Conformance

/-- One column as {lit}`PRAGMA table_xinfo` reports it: the name and declared type
as written ({lit}`""` for no type), NOT NULL, the default's text or none, and
{lit}`hidden`: 0 for an ordinary column, 2 for a {lit}`VIRTUAL` and 3 for a {lit}`STORED`
generated column (ADR 0014, D5). -/
structure NativeColumn where
  name : Identifier
  declaredType : String
  notNull : Bool
  defaultValue : Option String
  hidden : Nat := 0
  deriving Repr, DecidableEq

/-- The {lit}`hidden` value of {lit}`PRAGMA table_xinfo` for a catalog column: 2 for a
{lit}`VIRTUAL` and 3 for a {lit}`STORED` generated column, else 0. -/
def columnHidden (column : CatalogColumn) : Nat :=
  match column.generated with
  | some { stored := true, .. } => 3
  | some { stored := false, .. } => 2
  | none => 0

/-- One explicit index ({lit}`index_list` origin {lit}`c`): its name, the column position of
each key term, none for an expression ({lit}`index_xinfo` column -2), its uniqueness, the
sort order of each term, as an empty list when every term is ascending, whether it is
partial ({lit}`index_list` column {lit}`partial`), and the collation name of each term in
capitals ({lit}`index_xinfo` column {lit}`coll`), as an empty list when every term is
{lit}`BINARY`. -/
structure NativeIndex where
  name : Identifier
  columns : List (Option Nat)
  unique : Bool
  descending : List Bool := []
  isPartial : Bool := false
  collations : List String := []
  deriving Repr, DecidableEq

/-- The sort orders of the terms of an index as {name}`NativeIndex.descending` keeps them: the
empty list when every term is ascending. -/
def sortOrders (descending : List Bool) : List Bool := if descending.any id then descending else []

/-- The collation names of the terms of an index as {name}`NativeIndex.collations` keeps
them: the empty list when every term is {lit}`BINARY`. -/
def collationNames (names : List String) : List String := if names.all (· == "BINARY") then [] else names

/-- One native table: its name in {lit}`sqlite_schema`, its columns, the primary-key
positions in key order, the key positions of each UNIQUE constraint index (origin
{lit}`u`), its explicit indexes, its rows, and whether it is {lit}`WITHOUT ROWID`. The rows
of a {lit}`WITHOUT ROWID` table have the rowid 0: SQLite gives them no rowid. -/
structure NativeTable where
  name : Identifier
  columns : List NativeColumn
  primaryKey : List Nat
  uniqueKeys : List (List Nat)
  indexes : List NativeIndex
  rows : List Row
  withoutRowid : Bool := false
  deriving Repr, DecidableEq

/-- Where SQLite reported a statement's error: in {lit}`sqlite3_prepare_v2`, where
resolution decides it, or in {lit}`sqlite3_step`, where the execution semantics
decides it. -/
inductive ErrorPhase where
  /-- {lit}`sqlite3_prepare_v2` failed. -/
  | prepare
  /-- {lit}`sqlite3_step` failed. -/
  | step
  deriving Repr, DecidableEq

/-- Native truth after one statement. Extended codes are retained for diagnostics;
the model compares primary codes. {lit}`phase` is the phase of an error when the
recorder observed it; it is {name}`Option.none` without an error, and for records
from a recorder that did not observe phases. -/
structure NativeObservation where
  visible : List NativeTable
  persisted : List NativeTable
  transactionOpen : Bool
  primaryCode : Nat
  extendedCode : Nat
  phase : Option ErrorPhase := none
  deriving Repr, DecidableEq

/-- Insert a key into lexicographic order, with structural recursion the kernel reduces. -/
def insertKey (key : List Nat) : List (List Nat) → List (List Nat)
  | [] => [key]
  | head :: rest => if decide (key ≤ head) then key :: head :: rest else head :: insertKey key rest

/-- Keys in lexicographic order, so declaration order does not affect a comparison. -/
def sortKeys (keys : List (List Nat)) : List (List Nat) := keys.foldr insertKey []

/-- Keyword defaults whose spelling ignores ASCII case. SQLite treats each as a
keyword; quoted literals retain their delimiters and compare exactly instead. -/
def defaultKeywords : List String :=
  ["null", "true", "false", "current_timestamp", "current_time", "current_date"]

/-- Whether a catalog column matches its native metadata: the same name, the same
declared type text, NOT NULL, the same default spelling, and the same {lit}`hidden` value
({name}`columnHidden`). Keyword defaults ignore ASCII case; all other defaults keep
their exact source spelling. -/
def columnMatches (column : CatalogColumn) (native : NativeColumn) : Bool :=
  column.name == native.name && column.declaredType.getD "" == native.declaredType &&
  column.notNull == native.notNull && columnHidden column == native.hidden &&
  match column.defaultValue, native.defaultValue with
  | none, none => true
  | some written, some text =>
    if defaultKeywords.contains (normalizeIdentifier written.sourceText) then
      normalizeIdentifier written.sourceText == normalizeIdentifier text
    else written.sourceText == text
  | _, _ => false

/-- The explicit indexes of the table at a catalog position, as native metadata,
in folded-name order of the catalog. -/
def catalogIndexes (catalog : Catalog) (position : Nat) : List NativeIndex :=
  catalog.filterMap fun object => match object.entry with
    | .index index => if index.table == position then
        some { name := object.name, unique := index.unique, isPartial := index.filter.isSome,
               columns := index.keys.map fun key => match key.term with
                 | .column position => some position
                 | .expression _ => none,
               descending := sortOrders (index.keys.map (·.descending)),
               collations := collationNames (index.keys.map (·.collation.sqlName)) } else none
    | .table _ => none

/-- Whether two index lists hold the same indexes, in any order. -/
def sameIndexes (model native : List NativeIndex) : Bool :=
  model.length == native.length && model.all (native.contains ·)

/-- Whether the catalog table at a position, its object name and its stored rows match
a native table: name, columns, keys (the primary key without repeated columns, as
{lit}`PRAGMA table_xinfo` gives each column once), indexes, {lit}`WITHOUT ROWID`, and rows: by rowid, or
for a {lit}`WITHOUT ROWID` table by their cells in key order
({name}`Belay.Sqlite.Table.scanRows`), since the model's rowids of such a table are its
own. -/
def tableMatches (catalog : Catalog) (position : Nat) (name : Identifier) (table : CatalogTable)
    (rows : List Row) (native : NativeTable) : Bool :=
  name == native.name && table.columns.length == native.columns.length &&
  (table.columns.zip native.columns).all (fun (column, observed) => columnMatches column observed) &&
  table.primaryKey.eraseDups == native.primaryKey && sortKeys table.uniqueKeys == sortKeys native.uniqueKeys &&
  sameIndexes (catalogIndexes catalog position) native.indexes && table.withoutRowid == native.withoutRowid &&
  if table.withoutRowid then
    ({ shape := table, rows } : Table).scanRows.map (·.values) ==
      ({ shape := table, rows := native.rows } : Table).scanRows.map (·.values)
  else sortRows rows == sortRows native.rows

/-- Whether a model database matches the native tables: every catalog table has exactly
one native table with its folded name that matches it, no native table is outside the
catalog, the database has one row list for each catalog object, and an index object holds
no rows. -/
def tablesMatch (database : Database) (natives : List NativeTable) : Bool :=
  let tables := database.catalog.zipIdx.filterMap fun (object, position) => match object.entry with
    | .table table => some (position, object.name, table)
    | .index _ => none
  natives.length == tables.length &&
  tables.all (fun (position, name, table) =>
    match natives.filter (fun native => native.name.sameName name) with
    | [native] => tableMatches database.catalog position name table (database.rows.getD position []) native
    | _ => false) &&
  database.rows.length == database.catalog.length &&
  database.catalog.zipIdx.all (fun (object, position) => match object.entry with
    | .index _ => (database.rows.getD position []).isEmpty
    | .table _ => true)

end Belay.Sqlite.Conformance
