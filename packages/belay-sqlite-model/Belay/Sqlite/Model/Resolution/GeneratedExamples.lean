import Belay.Sqlite.Model.Resolution.Examples
import Belay.Sqlite.Model.SqlExecution

set_option doc.verso true

/-! Examples of generated columns (ADR 0014, slice 5), checked by {lit}`#guard` when the
package builds: the values of both kinds, also of a column that reads a generated column
declared after it; INSERT with and without a column list; UPDATE that recomputes a value; a
UNIQUE generated column; SQLite's prepare errors; and the restrictions. The authored corpus
of generated columns compares the same rules with SQLite. -/

namespace Belay.Sqlite.Model.Resolution.GeneratedExamples

open Belay.Sqlite.Model Syntax Belay.Sqlite.Model.Resolution.Examples

/-- An unqualified column. -/
def ref (name : Identifier) : Expr := .identifier name .none

/-- A column {lit}`name AS (expression)`, {lit}`STORED` when {lit}`stored`. -/
def gen (name : Identifier) (expression : Expr) (stored : Bool := false) (more : List ColumnConstraint := []) :
    ColumnDefinition :=
  { name, declaredType := some "INTEGER",
    constraints := .generated expression (if stored then some (name! "Stored") else none) :: more }

/-- {lit}`g(a INTEGER, c AS (b + 1), b AS (a * 2) STORED, u AS (a) UNIQUE)`: {lit}`c` reads {lit}`b`,
which comes after it. -/
def tableG : Syntax.Statement :=
  .createTable (name! "g") [column (name! "a") (some "INTEGER"),
    gen (name! "c") (.arithmetic .add (ref (name! "b")) (.numeric "1")),
    gen (name! "b") (.arithmetic .multiply (ref (name! "a")) (.numeric "2")) true,
    gen (name! "u") (ref (name! "a")) false [.unique]] []

/-- The schema of the examples: {name}`tableG`. -/
def tables : Catalog := catalogOf (schema [tableG])

/-- The cells of the rows of {lit}`g` after a script that succeeds, or none. -/
def rowsOf (script : List Syntax.Statement) : Option (List (List Value)) :=
  match migration tables script with
  | .resolved resolved _ => match runSql (bindValues resolved []) tables.emptyDatabase with
    | .success database => (database.table 0).map fun table => table.rows.map (·.values)
    | .failure .. | .pending .. => none
  | .restricted _ => none

/-- The statements of a script from {name}`tables`. -/
def resolvedOf (script : List Syntax.Statement) : List Resolved.Statement := statements (migration tables script)

-- The catalog keeps each kind; the generated values follow the dependencies.
#guard (match tables.head? with
  | some { entry := .table table, .. } => table.columns.map (·.generated.map (·.stored)) == [none, some false, some true, some false]
  | some { entry := .index _, .. } | some { entry := .trigger _, .. } | none => false)
#guard rowsOf [.insert (name! "g") (some [name! "a"]) [[.numeric "3"]] [] none []] ==
  some [[.integer 3, .integer 7, .integer 6, .integer 3]]
-- An INSERT without a column list fills only the columns that are not generated.
#guard rowsOf [.insert (name! "g") none [[.numeric "4"]] [] none []] == some [[.integer 4, .integer 9, .integer 8, .integer 4]]
#guard resolvedOf [.insert (name! "g") none [[.numeric "4"], [.numeric "5"]] [] none [] , .insert (name! "g") none [[.numeric "4", .numeric "1"]] [] none []]
  matches [_, .prepareError (.expression (.valueCount _ 1 2))]
#guard resolvedOf [.insert (name! "g") (some [name! "a", name! "b"]) [[.numeric "4", .numeric "1"]] [] none []] ==
  [.prepareError (.expression (.insertGenerated (name! "b")))]
-- UPDATE recomputes the generated values, and naming a generated column is a prepare error.
#guard rowsOf [.insert (name! "g") none [[.numeric "1"]] [] none [], .update (name! "g") [(name! "a", .numeric "5")] none []] ==
  some [[.integer 5, .integer 11, .integer 10, .integer 5]]
#guard resolvedOf [.update (name! "g") [(name! "c", .numeric "5")] none []] ==
  [.prepareError (.expression (.updateGenerated (name! "c")))]
-- A UNIQUE generated column constrains its values.
#guard rowsOf [.insert (name! "g") none [[.numeric "1"]] [] none [], .insert (name! "g") none [[.numeric "1"]] [] none []] == none

-- The computation of a generated value reduces in the kernel.
example : LiteralData.generatedCells [{ name := name! "a", declaredType := none },
    { name := name! "b", declaredType := some "INTEGER", generated := some { expression := .arithmetic .multiply (.column 0) (.literal (.integer 2)), stored := false } }]
    [.integer 4, .null] = [.integer 4, .integer 8] := by decide +kernel

/-- The prepare error of one CREATE TABLE, or none. -/
def errorOf (statement : Syntax.Statement) : Option PrepareError :=
  match statements (migration tables [statement]) with
  | [.prepareError error] => some error
  | _ => none

-- SQLite's prepare errors of definitions.
#guard errorOf (.createTable (name! "n") [column (name! "a"), gen (name! "b") (ref (name! "a")) false [.primaryKey false]] []) ==
  some (.expression .generatedInPrimaryKey)
#guard errorOf (.createTable (name! "n") [column (name! "a"), gen (name! "b") (ref (name! "a"))] [.primaryKey [name! "b"]]) ==
  some (.expression .generatedInPrimaryKey)
#guard errorOf (.createTable (name! "n") [column (name! "a"), gen (name! "b") (ref (name! "a")) false [.default (.numeric "1") "1"]] []) ==
  some (.expression .defaultOnGenerated)
#guard errorOf (.createTable (name! "n") [column (name! "a"), gen (name! "b") (ref (name! "rowid"))] []) ==
  some (.expression (.noSuchColumn (name! "rowid")))
#guard errorOf (.createTable (name! "n") [gen (name! "a") (.numeric "1")] []) == some (.expression .onlyGeneratedColumns)
#guard errorOf (.createTable (name! "n") [column (name! "a"), gen (name! "b") (.qualified (name! "n") (name! "a"))] []) ==
  some (.expression .qualifiedGenerated)
#guard errorOf (.createTable (name! "n") [column (name! "a"),
  gen (name! "b") (ref (name! "a")) false [.generated (.numeric "1") none]] []) ==
  some (.expression (.errorInGenerated (name! "b")))
-- A PRIMARY KEY column of type integer, in any case, is a rowid alias: the frontend gives
-- INTEGER GENERATED ALWAYS as INTEGER.
#guard (match (catalogOf (schema [.createTable (name! "r")
    [{ name := name! "a", declaredType := some "integer", constraints := [.primaryKey false] }] []])).head? with
  | some { entry := .table table, .. } => table.rowidAlias == some 0
  | some { entry := .index _, .. } | some { entry := .trigger _, .. } | none => false)
-- A quoted kind and a kind other than VIRTUAL and STORED are SQLite's error in generated column.
#guard errorOf (.createTable (name! "n") [column (name! "a"),
  { name := name! "b", declaredType := none, constraints := [.generated (ref (name! "a")) (some (name! "\"stored\""))] }] []) ==
  some (.expression (.errorInGenerated (name! "b")))
#guard errorOf (.createTable (name! "n") [column (name! "a"),
  { name := name! "b", declaredType := none, constraints := [.generated (ref (name! "a")) (some (name! "foo"))] }] []) ==
  some (.expression (.errorInGenerated (name! "b")))
#guard errorOf (.createTable (name! "n") [column (name! "a"), gen (name! "b") (.currentTime "CURRENT_TIMESTAMP")] []) ==
  some (.expression .nondeterministicGenerated)

-- Restrictions: a loop, a date and time function, a DO UPDATE of a generated column, and ADD COLUMN.
#guard reason (migration tables [.createTable (name! "n") [column (name! "a"), gen (name! "b") (ref (name! "c")),
  gen (name! "c") (ref (name! "b"))] []]) == RestrictionKind.generatedLoop.message
#guard reason (migration tables [.createTable (name! "n") [column (name! "a"), gen (name! "b") (.call "date" [ref (name! "a")])] []]) ==
  RestrictionKind.generatedFunction.message
#guard reason (migration tables [.insert (name! "g") (some [name! "a"]) [[.numeric "1"]]
  [{ target := some [name! "u"], action := .update [(name! "b", .numeric "1")] none }] none []]) ==
  RestrictionKind.upsertGenerated.message
#guard reason (migration tables [.addColumn (name! "g") (gen (name! "z") (ref (name! "a")))]) ==
  RestrictionKind.addColumnGenerated.message

end Belay.Sqlite.Model.Resolution.GeneratedExamples
