import Belay.Sqlite.Model.Queries.Fixtures.Examples
import Belay.Sqlite.Model.Queries.Select.ScopeOwn

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.SubqueryResolutionExamples

open Belay.Sqlite.Model Syntax

/-- A catalog with {lit}`t(k INTEGER, v TEXT)` at position 0 and
{lit}`u(x, s TEXT COLLATE NOCASE, k)` at position 1. -/
def catalog : Catalog :=
  [{ name := (name! "t"), entry := .table { columns := [{ name := (name! "k"), declaredType := some "INTEGER" },
      { name := (name! "v"), declaredType := some "TEXT" }] } },
   { name := (name! "u"), entry := .table { columns := [{ name := (name! "x"), declaredType := none },
      { name := (name! "s"), declaredType := some "TEXT", collation := .nocase }, { name := (name! "k"), declaredType := none }] } }]

/-- A name as written, without quotes. -/
def name (text : String) : Expr := .identifier (Identifier.ofString text) .none

/-- A result column written as an expression without an alias. -/
def written (value : Expr) : ResultColumn := .expression value none "e"

/-- A table reference without alias. -/
def table (text : String) : TableReference := { table := Identifier.ofString text, alias := none }

/-- {lit}`SELECT columns FROM t [WHERE filter]` with the subqueries. -/
def fromT (columns : List ResultColumn) (filter : Option Expr) (subqueries : List Subquery) : Syntax.Statement :=
  .select columns (some (table "t")) [] filter [] [] none none subqueries

/-- {lit}`SELECT columns FROM u [WHERE filter]` as a subquery inside the query {lit}`parent`. -/
def fromU (columns : List ResultColumn) (filter : Option Expr) (parent : Option Nat := none) : Subquery :=
  { columns, source := some (table "u"), joins := [], filter, groupBy := [], orderBy := [], limit := none,
    offset := none, parent }

/-- {lit}`JOIN u ON EXISTS (q)`, where {lit}`q` is subquery 0. -/
def joinOnExists : Join := { operator := [], source := table "u", condition := some (.exists 0), usingColumns := none }

-- The rows NEW and OLD of a trigger stay visible to GROUP BY and ORDER BY, and a source of a query around is dropped.
#guard (let source : ScopeSource := { name := Identifier.ofString "a", columns := [] }
    (Scope.ownSources [{ source with depth := 1 }, { source with trigger := true, depth := 1 }, source]).map
      (fun entry => (entry.depth, entry.trigger))) == [(1, true), (0, false)]

end Belay.Sqlite.Model.Resolution.SubqueryResolutionExamples
