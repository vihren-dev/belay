import Belay.Sqlite.Resolution.Catalog
import Belay.Sqlite.Resolution.PrepareErrors
import Belay.Sqlite.Resolution.ConflictPolicy
import Belay.Sqlite.Resolution.RestrictionText
import Belay.Sqlite.Resolution.QueryForm

set_option doc.verso true

/-! The result of name resolution. A resolved statement refers to catalog
positions instead of names, an INSERT row has one value for each table column, and
literal values are converted. A SQLite prepare error takes the place of the
statement that SQLite refuses to prepare. A model restriction refuses the whole
script: SQLite accepts that SQL, but the model does not describe it. -/

namespace Belay.Sqlite

/-- A model restriction: SQLite accepts the SQL, but the model does not describe
it, so the whole script is refused before any proof. The statement index and the
path of the node in the {name}`Syntax.Statement` locate the SQL for diagnostics. -/
structure Restriction where
  /-- The zero-based statement index. -/
  statement : Nat
  /-- Child positions from the statement to the refused node; empty for the statement. -/
  path : List Nat
  /-- Which restriction of the registry refuses the SQL. -/
  kind : RestrictionKind
  deriving Repr, DecidableEq

/-- The message of a restriction that users read: the message of its kind. -/
def Restriction.reason (restriction : Restriction) : String := restriction.kind.message

namespace Resolved

/-- One cell of a resolved INSERT row: a value that resolution computed and stored with the
column's affinity, or an expression that reads the statement's clock, such as a
{lit}`VALUES` item {lit}`CURRENT_TIMESTAMP` or an omitted column with that default, which the
execution evaluates at the statement's clock value and stores with the column's affinity.
An expression cell reads no column. Use {lean}`Cell.value` for a known value. -/
inductive Cell where
  /-- A value, stored with the column's affinity. -/
  | value (value : Value)
  /-- An expression that reads the clock and no column. -/
  | expression (expression : Expr)
  deriving Repr, DecidableEq

/-- One statement after name resolution. For example, an INSERT into the table at
catalog position 0 with one full row is {lean}`Statement.insert 0 [[Cell.value Value.null]] []`.
A write names its table by catalog position; execution reads the table's columns, keys
and conflict algorithms from the catalog of the database it runs on. -/
inductive Statement where
  /-- Create the named table at the catalog position, which is the end of the catalog. -/
  | createTable (position : Nat) (name : Identifier) (table : CatalogTable)
  /-- Create the named index at the catalog position, which is the end of the catalog. -/
  | createIndex (position : Nat) (name : Identifier) (index : CatalogIndex)
  /-- Append the column to the table at the catalog position. -/
  | addColumn (table : Nat) (column : CatalogColumn)
  /-- Start a transaction. -/
  | begin
  /-- Commit the transaction. -/
  | commit
  /-- Roll the transaction back. -/
  | rollback
  /-- Insert full rows, with one cell for each column in table order ({name}`Cell`), and
  keep every unique key of the table ({name}`Catalog.uniqueKeys`) unique. The
  {lit}`RETURNING` columns are an expression over the written row and its name each,
  none without {lit}`RETURNING`; the execution semantics does not read them. -/
  | insert (table : Nat) (rows : List (List Cell)) (returning : List (Expr × String))
  /-- In every row where the optional filter condition is true (every row without a
  filter), set each column position to its expression, evaluated on the old row and
  stored with the column's affinity. A literal update of slice 3a is the special case
  of {lit}`.literal` values and the filter {lit}`column = integer`. The unique keys and
  the {lit}`RETURNING` columns are as for INSERT. -/
  | update (table : Nat) (assignments : List (Nat × Expr)) (filter : Option Expr)
      (returning : List (Expr × String))
  /-- INSERT with {lit}`ON CONFLICT` clauses or a conflict algorithm other than ABORT: the
  rows as for {name}`Statement.insert`, the clauses in written order, and the statement's
  {lit}`OR` algorithm, if any. The algorithm of each constraint is
  {name}`Catalog.writePolicy` of that algorithm. Each row is handled by the first clause
  whose target key has a conflicting row, or else by the algorithms of the constraints
  that it fails. -/
  | upsert (table : Nat) (rows : List (List Cell)) (clauses : List ConflictClause)
      (returning : List (Expr × String)) (algorithm : Option ConflictAlgorithm)
  /-- Remove every row where the optional filter condition is true (every row without a
  filter). The {lit}`RETURNING` columns are evaluated on each removed row; the
  execution semantics does not read them. -/
  | delete (table : Nat) (filter : Option Expr) (returning : List (Expr × String))
  /-- SQLite refuses to prepare the statement with this error. -/
  | prepareError (error : PrepareError)
  /-- Run a query: it reads the database, changes nothing, and has result rows. -/
  | query (query : Query)
  deriving Repr, DecidableEq

end Resolved

/-- The result of resolving a script: the resolved statements and the catalog after
all of them succeed, or a model restriction. -/
inductive ResolveResult where
  /-- Every statement resolved; a statement that SQLite refuses is a prepare error. -/
  | resolved (statements : List Resolved.Statement) (catalog : Catalog)
  /-- The model does not describe the script. -/
  | restricted (restriction : Restriction)
  deriving Repr, DecidableEq

end Belay.Sqlite
