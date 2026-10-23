import Belay.Sqlite.Model.DatabaseConstraintChecks
import Belay.Sqlite.Model.ForeignKeysHold
import Belay.Sqlite.Model.SqlExecution
import Belay.Sqlite.Model.Resolution.Examples

set_option doc.verso true

/-! Examples of the facts of a valid and of an admitted database (ADR 0022, D1 and D2), each
checked by the kernel. Each database comes from a script that the model runs, so its catalog is
what SQLite would create; a failing case then replaces the rows of one table with rows that no
statement writes, as a pragma or another program could. -/

namespace Belay.Sqlite.Model.ValidityExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- A text literal. -/
def text (value : String) : Expr := .string value.toUTF8.toList

/-- A text value. -/
def textValue (value : String) : Value := .text value.toUTF8.toList

/-- A name as written, without quotes. -/
def name (value : String) : Expr := .identifier (Identifier.ofString value) .none

/-- A column with a declared type and constraints. -/
def typed (value : String) (declaredType : Option String) (constraints : List ColumnConstraint := []) :
    ColumnDefinition :=
  { name := Identifier.ofString value, declaredType, constraints }

/-- The database that the script builds from the empty database under the profile, or the
empty database when the script fails. -/
def built (script : List Syntax.Statement) (profile : Profile := defaults) : Database :=
  match runSql (statements (migration [] script profile)) {} with
  | .success database => database
  | .failure .. | .pending .. => {}

/-- The database with the rows of its first table replaced. -/
def withRows (database : Database) (rows : List Row) : Database := database.setRows 0 rows

/-- The guide's first example: the table {lit}`invoices` with a rowid alias, NOT NULL columns, a
CHECK and a default, and two rows. -/
def invoices : Database := built
  [.createTable (name! "invoices")
    [typed "id" (some "INTEGER") [.primaryKey false], typed "customer" (some "TEXT") [.notNull],
     typed "amount" (some "INTEGER") [.notNull, .check (.compare .ge (name "amount") (.numeric "0")) "amount >= 0"],
     typed "status" (some "TEXT") [.notNull, .default (text "open") "'open'"]] [],
   .insert (name! "invoices") (some [name! "id", name! "customer", name! "amount"])
    [[.numeric "1", text "acme", .numeric "10"], [.numeric "2", text "zeta", .numeric "0"]] []]

/-- A stored row with the rowid and the cells. -/
def stored (rowid : Int) (cells : List Value) : Row := { rowid, values := cells }

-- The script stores both rows, and the database is valid.
example : invoices.rows.getD 0 [] = [stored 1 [.integer 1, textValue "acme", .integer 10, textValue "open"],
    stored 2 [.integer 2, textValue "zeta", .integer 0, textValue "open"]] := by decide +kernel
example : invoices.Valid defaults := by decide +kernel

-- A catalog over the column limit of a profile, and a database with no row list for its table.
example : ¬invoices.Admitted lowered := by decide +kernel
example : ¬({ invoices with rows := [] } : Database).RowsShaped := by decide +kernel

-- A NULL in a NOT NULL column: admitted, not valid.
example : (withRows invoices [stored 1 [.integer 1, .null, .integer 10, textValue "open"]]).Admitted defaults ∧
    ¬(withRows invoices [stored 1 [.integer 1, .null, .integer 10, textValue "open"]]).NotNull ∧
    ¬(withRows invoices [stored 1 [.integer 1, .null, .integer 10, textValue "open"]]).Valid defaults := by
  decide +kernel
-- A CHECK that is false.
example : ¬(withRows invoices [stored 1 [.integer 1, textValue "acme", .integer (-1), textValue "open"]]).ChecksHold := by
  decide +kernel
-- Two equal rowids.
example : ¬(withRows invoices [stored 1 [.integer 1, textValue "a", .integer 1, textValue "open"],
    stored 1 [.integer 1, textValue "b", .integer 2, textValue "open"]]).RowidsDistinct := by decide +kernel
-- A rowid out of the signed 64-bit range.
example : ¬(withRows invoices [stored (2 ^ 63) [.integer (2 ^ 63), textValue "a", .integer 1, textValue "open"]]).RowidsInRange := by
  decide +kernel
-- A short row.
example : ¬(withRows invoices [stored 1 [.integer 1, textValue "a"]]).RowsWide := by decide +kernel
-- A text in an INTEGER column that INTEGER affinity would store as a number.
example : ¬(withRows invoices [stored 1 [.integer 1, textValue "a", textValue "10", textValue "open"]]).RowsStored := by
  decide +kernel
-- A rowid alias cell that is not the rowid.
example : ¬(withRows invoices [stored 1 [.integer 2, textValue "a", .integer 1, textValue "open"]]).RowsAliased := by
  decide +kernel

/-- {lit}`CREATE TABLE s(a INTEGER) STRICT`. -/
def strictTable : Database := built [.createTable (name! "s") [typed "a" (some "INTEGER")] [] { strict := true }]

-- A text in a STRICT INTEGER column: the cell is in its stored form, but does not fit the type.
example : (withRows strictTable [stored 1 [textValue "x"]]).RowsStored ∧
    ¬(withRows strictTable [stored 1 [textValue "x"]]).TypesFit := by decide +kernel

/-- {lit}`CREATE TABLE u(a UNIQUE, b TEXT COLLATE NOCASE UNIQUE)`. -/
def uniqueTable : Database := built
  [.createTable (name! "u") [typed "a" none [.unique], typed "b" (some "TEXT") [.collate (name! "NOCASE"), .unique]] []]

-- The script creates the tables and the index.
example : strictTable.catalog.length = 1 ∧ uniqueTable.catalog.length = 1 := by decide +kernel

-- Two rows equal on a UNIQUE column, and two texts equal under NOCASE; two NULLs do not conflict.
example : ¬(withRows uniqueTable [stored 1 [.integer 5, .null], stored 2 [.integer 5, .null]]).KeysUnique := by
  decide +kernel
example : ¬(withRows uniqueTable [stored 1 [.null, textValue "A"], stored 2 [.null, textValue "a"]]).KeysUnique := by
  decide +kernel
example : (withRows uniqueTable [stored 1 [.null, .null], stored 2 [.null, .null]]).KeysUnique := by decide +kernel

/-- {lit}`CREATE TABLE p(a, b)` and {lit}`CREATE UNIQUE INDEX pa ON p(a) WHERE b = 1`. -/
def partialIndex : Database := built
  [.createTable (name! "p") [typed "a" none, typed "b" none] [],
   .createIndex (name! "pa") true (name! "p") [{ expression := name "a", descending := false }]
     (some (.compare .eq (name "b") (.numeric "1")))]

-- Equal keys conflict when the filter is true for both rows, and not when it is false for one.
example : ¬(withRows partialIndex [stored 1 [.integer 7, .integer 1], stored 2 [.integer 7, .integer 1]]).KeysUnique := by
  decide +kernel
example : (withRows partialIndex [stored 1 [.integer 7, .integer 1], stored 2 [.integer 7, .integer 0]]).KeysUnique := by
  decide +kernel

/-- {lit}`CREATE TABLE p(id PRIMARY KEY)` with the row 1, {lit}`CREATE TABLE c(x REFERENCES p)`,
and the child value; foreign keys are off, so any child value is stored. -/
def keys (child : String) : Database := built
  [.createTable (name! "p") [typed "id" none [.primaryKey false]] [],
   .createTable (name! "c") [typed "x" none [.references (name! "p") [] .noAction .noAction]] [],
   .insert (name! "p") none [[.numeric "1"]] [], .insert (name! "c") none [[.numeric child]] []]

-- With foreign keys off, a child without a parent is stored: the database is valid, but its
-- foreign keys do not hold. A child with its parent satisfies them.
example : (keys "9").Valid defaults ∧ ¬(keys "9").ForeignKeysHold := by decide +kernel
example : (keys "1").rows.getD 1 [] = [stored 1 [.integer 1]] ∧ (keys "1").ForeignKeysHold := by decide +kernel

end Belay.Sqlite.Model.ValidityExamples
