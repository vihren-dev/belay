import Belay.Sqlite.Model.Resolution.Examples
import Belay.Sqlite.Model.SqlExecution

set_option doc.verso true

/-! Examples of DROP INDEX and DROP TABLE (ADR 0014, slice 7), checked by {lit}`#guard` when
the package builds: the positions that each DROP removes; statements on later objects after
a DROP; an index of a later table that keeps its table; a DROP that a ROLLBACK undoes; a
CREATE after a DROP of the same name; SQLite's prepare errors with and without
{lit}`IF EXISTS`; and the restriction. The authored corpus of DROP compares the same rules
with SQLite. -/

namespace Belay.Sqlite.Model.Resolution.DropExamples

open Belay.Sqlite.Model Syntax Belay.Sqlite.Model.Resolution.Examples

/-- The schema of the examples: {lit}`t(a INTEGER)` with the index {lit}`ti` on {lit}`a`, then
{lit}`u(x INTEGER)` with the unique index {lit}`ui` on {lit}`x`, at positions 0 to 3. -/
def tables : Catalog := catalogOf (schema [.createTable (name! "t") [column (name! "a") (some "INTEGER")] [],
  .createIndex (name! "ti") false (name! "t") [{ expression := .identifier (name! "a") .none, descending := false }] none,
  .createTable (name! "u") [column (name! "x") (some "INTEGER")] [],
  .createIndex (name! "ui") true (name! "u") [{ expression := .identifier (name! "x") .none, descending := false }] none])

/-- An INSERT of one integer into the table. -/
def insertInto (table : Identifier) (value : String) : Syntax.Statement :=
  .insert table none [[.numeric value]] [] none []

/-- The outcome of a script from {name}`tables` without rows, or none for a restriction. -/
def run (script : List Syntax.Statement) : Option Outcome :=
  match migration tables script with
  | .resolved resolved _ => some (runSql (bindValues resolved []) tables.emptyDatabase)
  | .restricted _ => none

/-- The object names of the catalog after a script that succeeds, or none. -/
def namesAfter (script : List Syntax.Statement) : Option (List Identifier) :=
  match run script with
  | some (.success database) => some (database.catalog.map (·.name))
  | some (.failure ..) | some (.pending ..) | none => none

/-- The position and reason of a failure, or none. -/
def failure (script : List Syntax.Statement) : Option (Nat × ExecutionError) :=
  match run script with
  | some (.failure position reason _) => some (position, reason)
  | some (.success _) | some (.pending ..) | none => none

/-- The prepare error of one statement from {name}`tables`, or none. -/
def errorOf (statement : Syntax.Statement) : Option PrepareError :=
  match statements (migration tables [statement]) with
  | [.prepareError error] => some error
  | _ => none

-- DROP TABLE removes the table and its index; DROP INDEX one index.
#guard statements (migration tables [.dropTable (name! "T") false]) == [.drop [0, 1]]
#guard statements (migration tables [.dropIndex (name! "ui") false]) == [.drop [3]]
#guard namesAfter [.dropTable (name! "t") false] == some [name! "u", name! "ui"]
-- The index of the later table keeps its table: a duplicate fails after the DROP.
#guard (match (tables.drop [0, 1]).getLast? with
  | some { entry := .index index, .. } => index.table == 0
  | some { entry := .table _, .. } | some { entry := .view _, .. } | some { entry := .trigger _, .. } | none => false)
#guard failure [.dropTable (name! "t") false, insertInto (name! "u") "1", insertInto (name! "u") "1"] ==
  some (2, .constraintViolation)
-- A ROLLBACK undoes the DROP; a CREATE after a DROP may reuse the name.
#guard namesAfter [.begin, .dropTable (name! "t") false, .rollback] == some [name! "t", name! "ti", name! "u", name! "ui"]
#guard namesAfter [.dropTable (name! "t") false, .createTable (name! "t") [column (name! "z")] []] ==
  some [name! "u", name! "ui", name! "t"]
-- A statement on the dropped table is SQLite's prepare error.
#guard statements (migration tables [.dropTable (name! "t") false, insertInto (name! "t") "1"]) ==
  [.drop [0, 1], .prepareError (.noSuchTable (name! "t"))]

-- SQLite's prepare errors, and IF EXISTS.
#guard errorOf (.dropTable (name! "nope") false) == some (.noSuchTable (name! "nope"))
#guard errorOf (.dropTable (name! "ti") false) == some (.noSuchTable (name! "ti"))
#guard statements (migration tables [.dropTable (name! "nope") true]) == [.drop []]
#guard errorOf (.dropIndex (name! "nope") false) == some (.noSuchIndex (name! "nope"))
#guard errorOf (.dropIndex (name! "t") false) == some (.noSuchIndex (name! "t"))
#guard statements (migration tables [.dropIndex (name! "u") true]) == [.drop []]
#guard errorOf (.dropTable (name! "Sqlite_Schema") true) == some (.tableMayNotBeDropped (name! "sqlite_master"))
#guard errorOf (.dropTable (name! "sqlite_temp_schema") false) == some (.tableMayNotBeDropped (name! "sqlite_temp_master"))

-- The restriction: the index of a constraint, which the catalog does not name.
#guard reason (migration tables [.dropIndex (name! "sqlite_autoindex_u_1") true]) ==
  RestrictionKind.dropConstraintIndex.message

end Belay.Sqlite.Model.Resolution.DropExamples
