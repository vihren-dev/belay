import Belay.Sqlite.Model.Resolution.Examples
import Belay.Sqlite.Model.SqlExecution

set_option doc.verso true

/-! Examples of CHECK constraints and foreign keys (ADR 0014, slice 4), checked by
{lit}`#guard` when the package builds: a CHECK that fails and one that NULL passes; the order
NOT NULL, CHECK, unique keys; the conflict algorithms; UPDATE and {lit}`DO UPDATE`;
ADD COLUMN over rows; a CREATE TABLE with constraints that runs; SQLite's prepare errors of
CHECK and foreign keys; and the restrictions. The authored corpus of CHECK constraints
compares the same rules with SQLite. -/

namespace Belay.Sqlite.Model.Resolution.CheckExamples

open Belay.Sqlite.Model Syntax Belay.Sqlite.Model.Resolution.Examples

/-- An unqualified column. -/
def ref (name : Identifier) : Expr := .identifier name .none

/-- {lit}`column > n`. -/
def above (name : Identifier) (n : String) : Expr := .compare .gt (ref name) (.numeric n)

/-- An INTEGER column with constraints. -/
def integer (name : Identifier) (constraints : List ColumnConstraint) : ColumnDefinition :=
  { name, declaredType := some "INTEGER", constraints }

/-- {lit}`k(a INTEGER CHECK (a > 0), b INTEGER NOT NULL ON CONFLICT IGNORE, CHECK (a != 5))`. -/
def tableK : Syntax.Statement :=
  .createTable (name! "k") [integer (name! "a") [.check (above (name! "a") "0") "a > 0"],
    integer (name! "b") [.notNull (some .ignore)]] [.check (.compare .ne (ref (name! "a")) (.numeric "5")) "a != 5"]

/-- {lit}`u(k INTEGER UNIQUE ON CONFLICT IGNORE, v INTEGER CHECK (v < 9))`. -/
def tableU : Syntax.Statement :=
  .createTable (name! "u") [integer (name! "k") [.unique (some .ignore)],
    integer (name! "v") [.check (.compare .lt (ref (name! "v")) (.numeric "9")) "v < 9"]] []

/-- The schema of the examples: {name}`tableK`, {name}`tableU`, {lit}`p(a INTEGER)` and
{lit}`c(a INTEGER CHECK (a > 0))`, whose UPDATE has no conflict algorithms. -/
def tables : Catalog := catalogOf (schema [tableK, tableU, .createTable (name! "p") [integer (name! "a") []] [],
  .createTable (name! "c") [integer (name! "a") [.check (above (name! "a") "0") "a > 0"]] []])

/-- An INSERT of one row of integer literals, with an optional {lit}`OR` algorithm. -/
def insertInto (table : Identifier) (cells : List Expr) (algorithm : Option ConflictAlgorithm := none) :
    Syntax.Statement :=
  .insert table none [cells] [] algorithm []

/-- The outcome of a script from {name}`tables` without rows, or none for a restriction. -/
def run (script : List Syntax.Statement) : Option Outcome :=
  match migration tables script with
  | .resolved resolved _ => some (runSql (bindValues resolved []) tables.emptyDatabase)
  | .restricted _ => none

/-- The position and reason of a failure, or none. -/
def failure (script : List Syntax.Statement) : Option (Nat × ExecutionError) :=
  match run script with
  | some (.failure position reason _) => some (position, reason)
  | some (.success _) | some (.pending ..) | none => none

/-- The position and reason of a failure, with the number of rows of the table at a catalog
position in the database that the failure keeps; none for a run that does not fail. -/
def failedRows (position : Nat) (script : List Syntax.Statement) : Option (Nat × ExecutionError × Option Nat) :=
  match run script with
  | some (.failure index reason database) => some (index, reason, (database.table position).map (·.rows.length))
  | some (.success _) | some (.pending ..) | none => none

/-- The cells of the rows of the table at a catalog position after a run that succeeds. -/
def rowsAt (position : Nat) (script : List Syntax.Statement) : Option (List (List Value)) :=
  match run script with
  | some (.success database) => (database.table position).map fun table => table.rows.map (·.values)
  | some (.failure ..) | some (.pending ..) | none => none

-- A CHECK fails when its condition is false; NULL passes; a table CHECK checks too.
#guard failure [insertInto (name! "k") [.numeric "0", .numeric "1"]] == some (0, .constraintViolation)
#guard rowsAt 0 [insertInto (name! "k") [.null, .numeric "1"]] == some [[.null, .integer 1]]
#guard failure [insertInto (name! "k") [.numeric "5", .numeric "1"]] == some (0, .constraintViolation)
-- NOT NULL comes first: its IGNORE skips a row that also fails a CHECK.
#guard rowsAt 0 [insertInto (name! "k") [.numeric "0", .null]] == some []
-- CHECK comes before the unique keys: a row that conflicts under IGNORE and fails a CHECK fails.
#guard failure [insertInto (name! "u") [.numeric "1", .numeric "1"], insertInto (name! "u") [.numeric "1", .numeric "9"]] ==
  some (1, .constraintViolation)
#guard rowsAt 1 [insertInto (name! "u") [.numeric "1", .numeric "1"], insertInto (name! "u") [.numeric "1", .numeric "2"]] ==
  some [[.integer 1, .integer 1]]
-- OR IGNORE skips the row; REPLACE acts as ABORT; FAIL keeps the rows before.
#guard rowsAt 0 [insertInto (name! "k") [.numeric "0", .numeric "1"] (some .ignore)] == some []
#guard failure [insertInto (name! "k") [.numeric "0", .numeric "1"] (some .replace)] == some (0, .constraintViolation)
#guard failedRows 0 [.insert (name! "k") none [[.numeric "1", .numeric "1"], [.numeric "0", .numeric "1"]] [] (some .fail) []] ==
  some (0, .constraintFail, some 1)
-- UPDATE and DO UPDATE check the new rows.
#guard failure [insertInto (name! "c") [.numeric "1"],
  .update (name! "c") [(name! "a", .numeric "0")] none []] == some (1, .constraintViolation)
#guard failure [insertInto (name! "u") [.numeric "1", .numeric "1"],
  .insert (name! "u") none [[.numeric "1", .numeric "1"]]
    [{ target := some [name! "k"], action := .update [(name! "v", .numeric "10")] none }] none []] ==
  some (1, .constraintViolation)

-- ADD COLUMN checks the rows with the new default: SQLite's error at step (code 1); an empty
-- table succeeds.
#guard failure [insertInto (name! "p") [.numeric "1"],
  .addColumn (name! "p") (integer (name! "c") [.default (.numeric "5") "5", .check (above (name! "c") "9") "c > 9"])] ==
  some (1, .checkColumnDefault)
#guard failure [.addColumn (name! "p") (integer (name! "c") [.default (.numeric "5") "5", .check (above (name! "c") "9") "c > 9"]),
  insertInto (name! "p") [.numeric "1", .numeric "10"]] == none

-- A CREATE TABLE with constraints runs, and its keys and CHECK constraints apply.
#guard failure [.createTable (name! "n") [integer (name! "a") [.primaryKey false, .check (above (name! "a") "0") "a > 0"]] [],
  insertInto (name! "n") [.numeric "1"], insertInto (name! "n") [.numeric "1"]] == some (2, .constraintViolation)
#guard failure [.createTable (name! "n") [integer (name! "a") [.check (above (name! "a") "0") "a > 0"]] [],
  insertInto (name! "n") [.numeric "0"]] == some (1, .constraintViolation)

/-- The prepare error of one CREATE TABLE, or none. -/
def errorOf (statement : Syntax.Statement) : Option PrepareError :=
  match statements (migration tables [statement]) with
  | [.prepareError error] => some error
  | _ => none

-- SQLite's prepare errors: a CHECK of no column, an aggregate in a CHECK, and the three of
-- foreign keys; a missing referenced table is admitted.
#guard errorOf (.createTable (name! "x") [integer (name! "a") [.check (above (name! "zz") "0") "zz > 0"]] []) ==
  some (.expression (.noSuchColumn (name! "zz")))
#guard (errorOf (.createTable (name! "x") [integer (name! "a") [.check (.callStar "count") "count(*)"]] [])).isSome
#guard errorOf (.createTable (name! "x") [integer (name! "a") [.references (name! "q") [name! "x", name! "y"] .noAction .noAction]] []) ==
  some (.expression (.foreignKeyOneColumn (name! "a") (name! "q")))
#guard errorOf (.createTable (name! "x") [integer (name! "a") []] [.foreignKey [name! "a"] (name! "q") [name! "x", name! "y"] .noAction .noAction]) ==
  some (.expression .foreignKeyColumnCount)
#guard errorOf (.createTable (name! "x") [integer (name! "a") []] [.foreignKey [name! "zz"] (name! "q") [] .noAction .noAction]) ==
  some (.expression (.unknownForeignKeyColumn (name! "zz")))
#guard errorOf (.createTable (name! "x") [integer (name! "a") [.references (name! "nothere") [name! "x"] .cascade .noAction]] []) == none
-- The catalog keeps each foreign key with its actions, for {lit}`PRAGMA foreign_key_list`:
-- a column's, then the table constraints'.
#guard (match (catalogOf (schema [.createTable (name! "x") [integer (name! "a") [.references (name! "p") [] .cascade .setNull],
    integer (name! "b") []] [.foreignKey [name! "b", name! "a"] (name! "q") [name! "m", name! "n"] .noAction .restrict]])).head? with
  | some { entry := .table table, .. } => table.allForeignKeys ==
    [{ table := name! "p", columns := [0], referenced := [], onDelete := .cascade, onUpdate := .setNull },
     { table := name! "q", columns := [1, 0], referenced := [name! "m", name! "n"], onDelete := .noAction, onUpdate := .restrict }]
  | some { entry := .index _, .. } | some { entry := .trigger _, .. } | none => false)
#guard (PrepareError.expression (.unknownForeignKeyColumn (name! "zz"))).message ==
  "unknown column \"zz\" in foreign key definition"
-- The CHECK resolves after the other checks of the definition.
#guard errorOf (.createTable (name! "x") [integer (name! "a") [.check (above (name! "zz") "0") "zz > 0"],
  integer (name! "a") []] []) == some (.expression (.duplicateColumn (name! "a")))

-- Restrictions: a time keyword in a CHECK, and a CHECK of ADD COLUMN that SQLite cannot resolve.
#guard reason (migration tables [.createTable (name! "x")
    [integer (name! "a") [.check (.isNull (.currentTime "CURRENT_TIMESTAMP") true) "CURRENT_TIMESTAMP IS NOT NULL"]] []]) ==
  RestrictionKind.checkFunction.message
#guard reason (migration tables [.addColumn (name! "p") (integer (name! "c") [.check (above (name! "zz") "0") "zz > 0"])]) ==
  RestrictionKind.addColumnCheckError.message

end Belay.Sqlite.Model.Resolution.CheckExamples
