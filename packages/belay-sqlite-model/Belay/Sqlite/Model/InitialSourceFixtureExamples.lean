import Belay.Sqlite.Model.Resolution.CommonTableResolutionExamples

set_option doc.verso true

/-! Helpers for the examples of the initial-database source (ADR 0017, S6): databases written as
model values, and query syntax with a source in the schema {lit}`before`. The examples in
{lit}`InitialSourceExamples.lean`, {lit}`TwoStateExamples.lean` and {lit}`TwoStateViewExamples.lean`
use them. -/

namespace Belay.Sqlite.Model.TwoStateFixtures

open Syntax Resolution.Examples Resolution.CollationExamples Resolution.CompoundResolutionExamples

/-- A column with a declared type, which is {lit}`INTEGER` unless another one is given. -/
def col (name : String) (type : Option String := some "INTEGER") (collation : Collation := .binary) : CatalogColumn :=
  { name := Identifier.ofString name, declaredType := type, collation }

/-- A table with its rows, whose rowids are 1, 2, and so on. With an alias position, the column at
that position is the primary key and the alias of the rowid. -/
def tableOf (name : String) (columns : List CatalogColumn) (rows : List (List Value)) (alias : Option Nat := none) :
    Identifier × Table :=
  (Identifier.ofString name,
    { shape := { columns, rowidAlias := alias, primaryKey := alias.toList },
      rows := rows.zipIdx.map fun (values, index) => { rowid := ((index + 1 : Nat) : Int), values } })

/-- The database of tables that the given table list names, at positions 0, 1, and so on. -/
def databaseOf (tables : List (Identifier × Table)) : Database := Database.ofTables tables

/-- The text value of a string. -/
def text (value : String) : Value := Value.text value.toUTF8.toList

/-- The context of the fixtures: the pinned profile, with statements that run. -/
def context : ResolveContext := { profile := Profile.pinned, mode := .execution }

/-- The table {lit}`before.table`, with an optional alias. -/
def before (table : String) (alias : Option String := none) : TableReference :=
  { table := Identifier.ofString table, alias := alias.map Identifier.ofString, schema := some initialSchemaName }

/-- The table {lit}`table` of the current database, with an optional alias. -/
def now (table : String) (alias : Option String := none) : TableReference :=
  { table := Identifier.ofString table, alias := alias.map Identifier.ofString }

/-- A column that an unqualified name reads. -/
def cell (name : String) : ResultColumn := shown (ref (Identifier.ofString name))

/-- A column that {lit}`source.name` reads. -/
def cellOf (source name : String) : ResultColumn :=
  shown (.qualified (Identifier.ofString source) (Identifier.ofString name))

/-- The expression {lit}`name` as written. -/
def named' (name : String) : Expr := ref (Identifier.ofString name)

/-- The expression {lit}`source.name`. -/
def dotted (source name : String) : Expr := .qualified (Identifier.ofString source) (Identifier.ofString name)

/-- A {lit}`SELECT` of the columns from the source, ordered by the terms. -/
def select (columns : List ResultColumn) (source : Option TableReference) (joins : List Join := [])
    (filter : Option Expr := none) (orderBy : List OrderTerm := []) (subqueries : List Subquery := []) :
    Syntax.Statement :=
  .select columns source joins filter [] orderBy none none subqueries

/-- A {lit}`SELECT` that orders by its column {lit}`a`. -/
def selectA (source : TableReference) (filter : Option Expr := none) : Syntax.Statement :=
  select [cell "a"] (some source) [] filter [ascending (named' "a")]

/-- Integer cells in a list of rows. -/
def ints (rows : List (List Int)) : List (List Value) := rows.map (·.map Value.integer)

/-- {lit}`t(a INTEGER)` with the rows 1 and 2: the initial database of most fixtures. -/
def initialT : Database := databaseOf [tableOf "t" [col "a"] (ints [[1], [2]])]

/-- {lit}`t(a INTEGER)` with the row 3: a current database that differs from {name}`initialT`. -/
def currentT : Database := databaseOf [tableOf "t" [col "a"] (ints [[3]])]

/-- A query of the columns from one source, without joins, filter or order. -/
def subqueryOf (columns : List ResultColumn) (source : TableReference) : Subquery :=
  { columns, source := some source, joins := [], filter := none, groupBy := [], orderBy := [], limit := none,
    offset := none, parent := none }

end Belay.Sqlite.Model.TwoStateFixtures
