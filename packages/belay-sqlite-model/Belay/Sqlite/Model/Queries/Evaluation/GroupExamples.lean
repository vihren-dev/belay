import Belay.Sqlite.Model.Queries.Fixtures.Examples
import Belay.Sqlite.Model.Shared.Execution.Execution

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.GroupExamples

open Belay.Sqlite.Model Syntax

/-- The table {lit}`t` of the examples. -/
def table : Table where
  shape := { columns := [{ name := (name! "g"), declaredType := none }, { name := (name! "v"), declaredType := some "INTEGER" },
    { name := (name! "s"), declaredType := some "TEXT", collation := .nocase }] }
  rows := [⟨1, [.integer 1, .integer 10, .text [97]]⟩, ⟨2, [.integer 1, .integer 20, .text [65]]⟩,
    ⟨3, [.integer 2, .integer 5, .text [98]]⟩, ⟨4, [.integer 3, .null, .text [99]]⟩]

/-- The database with {lit}`t` at catalog position 0. -/
def database : Database := .ofTables [((name! "t"), table)]

/-- A name as written, without quotes. -/
def col (text : String) : Expr := .identifier (Identifier.ofString text) .none

/-- A result column written as an expression without an alias. -/
def written (value : Expr) : ResultColumn := .expression value none "e"

/-- {lit}`SELECT columns FROM t [GROUP BY] [HAVING] [ORDER BY]` with {lit}`DISTINCT`. -/
def query (columns : List ResultColumn) (groupBy : List Expr := []) (having : Option Expr := none)
    (orderBy : List OrderTerm := []) (distinct : Bool := false) : Syntax.Statement :=
  .select columns (some { table := Identifier.ofString "t", alias := none }) [] none groupBy orderBy none none [] having
    distinct

/-- What a statement of the examples gives: its result rows, a prepare error, or a model
restriction (or another statement). -/
inductive Answer where
  /-- The result rows of a query. -/
  | rows (rows : List (List Value))
  /-- SQLite's prepare error. -/
  | error (error : PrepareError)
  /-- A model restriction, or a statement that is no query. -/
  | restricted
  deriving DecidableEq

/-- {lit}`count(*)`, written as a call. -/
def count : Expr := .callStar "count"

/-- An ascending {lit}`ORDER BY` term. -/
def by_ (expression : Expr) : OrderTerm := { expression, descending := false }

end Belay.Sqlite.Model.Resolution.GroupExamples
