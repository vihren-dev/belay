import Belay.Sqlite.Model.Schema.Rows.DatabaseConstraintChecks
import Belay.Sqlite.Model.Schema.Rows.ForeignKeyFacts
import Belay.Sqlite.Model.Schema.Dispatch.Examples
import Belay.Sqlite.Model.Queries.Preparation.ValidityExamples
import Belay.Sqlite.Model.Schema.Dispatch.SqlAdvance

set_option doc.verso true

namespace Belay.Sqlite.Model.ValidityExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- A column with a declared type and constraints. -/
def typed (value : String) (declaredType : Option String) (constraints : List ColumnConstraint := []) :
    ColumnDefinition :=
  { name := Identifier.ofString value, declaredType, constraints }

/-- The database that the script builds from the empty database under the profile, or the
empty database when the script fails. -/
def built (script : List Syntax.Statement) (profile : Profile := defaults) : Database :=
  match runSql (bindValues (statements (migration [] script profile)) []) {} with
  | .success database => database
  | .failure .. | .pending .. => {}

/-- {lit}`CREATE TABLE s(a INTEGER) STRICT`. -/
def strictTable : Database := built [.createTable (name! "s") [typed "a" (some "INTEGER")] [] { strict := true }]

/-- {lit}`CREATE TABLE u(a UNIQUE, b TEXT COLLATE NOCASE UNIQUE)`. -/
def uniqueTable : Database := built
  [.createTable (name! "u") [typed "a" none [.unique], typed "b" (some "TEXT") [.collate (name! "NOCASE"), .unique]] []]

-- The script creates the tables and the index.
example : strictTable.catalog.length = 1 ∧ uniqueTable.catalog.length = 1 := by decide +kernel

/-- {lit}`CREATE TABLE p(a, b)` and {lit}`CREATE UNIQUE INDEX pa ON p(a) WHERE b = 1`. -/
def partialIndex : Database := built
  [.createTable (name! "p") [typed "a" none, typed "b" none] [],
   .createIndex (name! "pa") true (name! "p") [{ expression := name "a", descending := false }]
     (some (.compare .eq (name "b") (.numeric "1")))]

end Belay.Sqlite.Model.ValidityExamples
