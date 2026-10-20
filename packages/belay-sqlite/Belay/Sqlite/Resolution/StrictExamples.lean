import Belay.Sqlite.Resolution.Examples
import Belay.Sqlite.SqlExecution

set_option doc.verso true

/-! Examples of {lit}`STRICT` tables (ADR 0014, slice 6), checked by {lit}`#guard` when the
package builds: each type with a value that fits after its affinity and one that does not;
NULL; {lit}`ANY` without affinity, also in a default; the order NOT NULL, type, CHECK; the
conflict algorithms, which all act as ABORT for a type error; UPDATE; {lit}`STRICT, WITHOUT
ROWID`; SQLite's prepare errors; and the restriction of ADD COLUMN. The authored corpus of
{lit}`STRICT` tables compares the same rules with SQLite. -/

namespace Belay.Sqlite.Resolution.StrictExamples

open Belay.Sqlite Syntax Belay.Sqlite.Resolution.Examples

/-- An unqualified column. -/
def ref (name : Identifier) : Expr := .identifier name .none

/-- The options of a {lit}`STRICT` table. -/
def strict : TableOptions := { strict := true }

/-- {lit}`s(i INTEGER, r REAL, t TEXT, b BLOB, a ANY) STRICT`. -/
def tableS : Syntax.Statement :=
  .createTable (name! "s") [column (name! "i") (some "INTEGER"), column (name! "r") (some "REAL"),
    column (name! "t") (some "TEXT"), column (name! "b") (some "BLOB"),
    { name := name! "a", declaredType := some "ANY", constraints := [.default (.string [55]) "'7'"] }] [] strict

/-- {lit}`c(k INTEGER NOT NULL ON CONFLICT IGNORE, v INTEGER CHECK (v > 0)) STRICT`. -/
def tableC : Syntax.Statement :=
  .createTable (name! "c") [{ name := name! "k", declaredType := some "INTEGER", constraints := [.notNull (some .ignore)] },
    { name := name! "v", declaredType := some "INTEGER",
      constraints := [.check (.compare .gt (ref (name! "v")) (.numeric "0")) "v > 0"] }] [] strict

/-- {lit}`w(k TEXT PRIMARY KEY, v INT) STRICT, WITHOUT ROWID`. -/
def tableW : Syntax.Statement :=
  .createTable (name! "w") [{ name := name! "k", declaredType := some "TEXT", constraints := [.primaryKey false] },
    column (name! "v") (some "INT")] [] { strict := true, withoutRowid := true }

/-- The schema of the examples: {name}`tableS`, {name}`tableC` and {name}`tableW`. -/
def tables : Catalog := catalogOf (schema [tableS, tableC, tableW])

/-- An INSERT of one row with an optional {lit}`OR` algorithm. -/
def insertInto (table : Identifier) (cells : List Expr) (algorithm : Option ConflictAlgorithm := none) :
    Syntax.Statement :=
  .insert table none [cells] [] algorithm []

/-- The outcome of a script from {name}`tables` without rows, or none for a restriction. -/
def run (script : List Syntax.Statement) : Option Outcome :=
  match migration tables script with
  | .resolved resolved _ => some (runSql resolved tables.emptyDatabase)
  | .restricted _ => none

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

/-- One row of {lit}`s` with the cells, the others NULL, in the column order of {name}`tableS`. -/
def rowS (i r t b a : Expr) : Syntax.Statement := insertInto (name! "s") [i, r, t, b, a]

-- The catalog keeps the strict types.
#guard (match tables.head? with
  | some { entry := .table table, .. } =>
    table.strict && table.columns.map (·.strictType) == [some .integer, some .real, some .text, some .blob, some .any]
  | some { entry := .index _, .. } | none => false)
-- Values that fit after affinity: text that reads as an integer, an integer as REAL, a number as TEXT.
#guard rowsAt 0 [rowS (.string [32, 55, 32]) (.numeric "4") (.numeric "5") (.blob [0]) (.string [54])] ==
  some [[.integer 7, .real (4.0 : Float).toBits, .text [53], .blob [0], .text [54]]]
-- NULL fits every type that has no NOT NULL.
#guard rowsAt 0 [rowS .null .null .null .null .null] == some [[.null, .null, .null, .null, .null]]
-- ANY keeps its default as text, without affinity.
#guard rowsAt 0 [.insert (name! "s") (some [name! "i"]) [[.numeric "1"]] [] none []] ==
  some [[.integer 1, .null, .null, .null, .text [55]]]
-- A value that does not fit: text in INTEGER, a blob in REAL and in TEXT, an integer in BLOB.
#guard failedRows 0 [rowS (.string [120]) .null .null .null .null] == some (0, .constraintViolation, some 0)
#guard failedRows 0 [rowS .null (.blob [1]) .null .null .null] == some (0, .constraintViolation, some 0)
#guard failedRows 0 [rowS .null .null (.blob [1]) .null .null] == some (0, .constraintViolation, some 0)
#guard failedRows 0 [rowS .null .null .null (.numeric "1") .null] == some (0, .constraintViolation, some 0)
-- NOT NULL comes first: its IGNORE skips a row that also has a type error.
#guard rowsAt 1 [insertInto (name! "c") [.null, .string [120]]] == some []
-- The type comes before CHECK: a type error that also fails the CHECK is the type error.
#guard failedRows 1 [insertInto (name! "c") [.numeric "1", .string [120]]] == some (0, .constraintViolation, some 0)
-- Every algorithm acts as ABORT: IGNORE fails, and FAIL keeps no earlier row.
#guard failedRows 0 [insertInto (name! "s") [.string [120], .null, .null, .null, .null] (some .ignore)] ==
  some (0, .constraintViolation, some 0)
#guard failedRows 0 [insertInto (name! "s") [.string [120], .null, .null, .null, .null] (some .replace)] ==
  some (0, .constraintViolation, some 0)
#guard failedRows 0 [.insert (name! "s") none [[.numeric "1", .null, .null, .null, .null],
  [.string [120], .null, .null, .null, .null]] [] (some .fail) []] == some (0, .constraintViolation, some 0)
-- UPDATE checks the new rows.
#guard failedRows 0 [rowS (.numeric "1") .null .null .null .null,
  .update (name! "s") [(name! "t", .blob [3])] none []] == some (1, .constraintViolation, some 1)
-- A STRICT WITHOUT ROWID table checks its types too.
#guard rowsAt 2 [insertInto (name! "w") [.numeric "1", .string [50]]] == some [[.text [49], .integer 2]]
#guard failedRows 2 [insertInto (name! "w") [.string [107], .string [120]]] == some (0, .constraintViolation, some 0)

/-- The prepare error of one statement from {name}`tables`, or none. -/
def errorOf (statement : Syntax.Statement) : Option PrepareError :=
  match statements (migration tables [statement]) with
  | [.prepareError error] => some error
  | _ => none

-- SQLite's prepare errors: a type that STRICT does not admit, and a column without a type.
#guard errorOf (.createTable (name! "n") [column (name! "a") (some "VARCHAR(10)")] [] strict) ==
  some (.expression (.unknownDatatype (name! "n") (name! "a") "VARCHAR(10)"))
#guard errorOf (.createTable (name! "n") [column (name! "a") none, column (name! "b") (some "INTEGER")] [] strict) ==
  some (.expression (.missingDatatype (name! "n") (name! "a")))
-- A table that is not STRICT admits every type.
#guard errorOf (.createTable (name! "n") [column (name! "a") (some "VARCHAR(10)")] []) == none

-- Restrictions: ADD COLUMN of a type that STRICT does not admit, and of a default that does
-- not fit; both are SQLite errors only while the statement runs.
#guard reason (migration tables [.addColumn (name! "s") (column (name! "z") (some "VARCHAR(5)"))]) ==
  RestrictionKind.addColumnStrictType.message
#guard reason (migration tables [.addColumn (name! "s")
  { name := name! "z", declaredType := some "INTEGER", constraints := [.default (.string [120]) "'x'"] }]) ==
  RestrictionKind.addColumnStrictType.message
-- An added ANY column keeps its text default.
#guard rowsAt 0 [rowS (.numeric "1") .null .null .null .null,
  .addColumn (name! "s") { name := name! "z", declaredType := some "ANY", constraints := [.default (.string [55]) "'7'"] }] ==
  some [[.integer 1, .null, .null, .null, .null, .text [55]]]

end Belay.Sqlite.Resolution.StrictExamples
