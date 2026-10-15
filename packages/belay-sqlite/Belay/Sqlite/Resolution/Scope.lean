import Belay.Sqlite.Resolution.Catalog

set_option doc.verso true

/-! The names in scope of an expression (ADR 0012, amendment 2, "Names"): the sources of
a query or the one table of a write, each with its name and columns. A joined row is
the concatenation of the cells of the sources in order, so a column has a position in
that row. -/

namespace Belay.Sqlite

/-- One named source: the name that qualifies its columns (the alias, or else the table
name, as written) and its columns. -/
structure Source where
  /-- The name of the source. -/
  name : String
  /-- The columns of the source's table. -/
  columns : List CatalogColumn
  deriving Repr, DecidableEq

/-- The sources in scope, in {lit}`FROM` order; empty where no table is in scope, as in
a {lit}`VALUES` row. -/
abbrev Scope := List Source

/-- The scope of one table under its name, as a write or a query of one table has. -/
def Scope.single (name : String) (columns : List CatalogColumn) : Scope := [{ name, columns }]

/-- The columns of all sources, in the order of the concatenated row. -/
def Scope.columns (scope : Scope) : List CatalogColumn := scope.flatMap (·.columns)

/-- The positions in the concatenated row of the columns that an unqualified name
names: the first column with the folded name in each source that has one. One position
is a name; none is a missing name; two or more are SQLite's
{lit}`ambiguous column name`. -/
def Scope.matches (scope : Scope) (name : String) : List Nat :=
  (scope.foldl (fun (offset, found) source =>
    (offset + source.columns.length, found ++ ((columnPosition source.columns name).map (offset + ·)).toList))
    (0, [])).2

/-- The offset in the concatenated row and the columns of the first source whose folded
name is the given name, where the first source of the scope starts at {lit}`offset`. -/
def Scope.sourceFrom (name : String) (offset : Nat) : Scope → Option (Nat × List CatalogColumn)
  | [] => none
  | source :: rest =>
    if normalizeIdentifier source.name == normalizeIdentifier name then some (offset, source.columns)
    else Scope.sourceFrom name (offset + source.columns.length) rest

/-- The offset in the concatenated row and the columns of the first source whose folded
name is the given name, as {lit}`source.*` and qualified names need. -/
def Scope.source? (scope : Scope) (name : String) : Option (Nat × List CatalogColumn) :=
  Scope.sourceFrom name 0 scope

/-- The position in the concatenated row of {lit}`source.column`, or none when no source
has the name or the source has no such column. -/
def Scope.qualified (scope : Scope) (source column : String) : Option Nat :=
  (scope.source? source).bind fun (offset, columns) => (columnPosition columns column).map (offset + ·)

end Belay.Sqlite
