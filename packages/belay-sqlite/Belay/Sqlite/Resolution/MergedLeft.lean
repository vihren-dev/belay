import Belay.Sqlite.Resolution.Values
import Belay.Sqlite.Resolution.Scope
import Belay.Sqlite.Resolution.Syntax

set_option doc.verso true

/-! The left side of a generated {lit}`USING` or {lit}`NATURAL` equality (ADR 0012,
amendments 2 and 3). Without right and full joins in the {lit}`FROM`, it is the left-most
left column of the name (slice 4b). With one anywhere, also after the join, SQLite
compares the coalesce of every left column of the name, and requires every left table
after the first with the name to merge it by its own join, else
{lit}`ambiguous reference to a in USING()` (slice 4d, checked on native 3.51.0). -/

namespace Belay.Sqlite

/-- The name of the left-most source of the scope with a column of the folded name, and
that column's name as declared; none when no source has one. A merged column has a
column of the same name in an earlier source, so the result is never merged. -/
def Scope.leftMost (scope : Scope) (name : String) : Option (String × String) :=
  scope.findSome? fun source =>
    (columnPosition source.columns name).bind fun position =>
      source.columns[position]?.map fun column => (source.name, column.name)

/-- Every column of the folded name in the scope, in order: the source's name, the
column's name as declared, and whether the source's join merged it. -/
def Scope.namedColumns (scope : Scope) (name : String) : List (String × String × Bool) :=
  scope.filterMap fun source => (columnPosition source.columns name).bind fun index =>
    source.columns[index]?.map fun column => (source.name, column.name, source.merged.contains index)

/-- A merged name, as written, when every left column of the name after the first is
merged by its own source's join; else SQLite's
{name}`PrepareError.ambiguousUsingReference`. SQLite checks it when the {lit}`FROM` has a
right or full join. -/
def usingReferenceChecked (left : Scope) (name : String) : Except ValueIssue String :=
  if ((left.namedColumns name).drop 1).all (·.2.2) then .ok name
  else .error (.prepare (.ambiguousUsingReference name))

/-- The coalesce of qualified columns, as written syntax: {lit}`COALESCE(s.c, …)` of the
first column and the others in order; one column is its qualified name. -/
def qualifiedCoalesce : String × String × Bool → List (String × String × Bool) → Syntax.Expr
  | (source, column, _), [] => .qualified source column
  | (source, column, _), next :: rest => .callPair "coalesce" (.qualified source column) (qualifiedCoalesce next rest)

/-- The left side of the generated equality of a merged name, as written syntax: with
{lit}`coalesced` (a right or full join in the {lit}`FROM`), the coalesce of every left
column of the name ({name}`qualifiedCoalesce`); else the left-most left column
({name}`Scope.leftMost`). None when the left input has no column of the name. -/
def mergedLeft (coalesced : Bool) (left : Scope) (name : String) : Option Syntax.Expr :=
  if coalesced then match left.namedColumns name with
    | [] => none
    | first :: rest => some (qualifiedCoalesce first rest)
  else (left.leftMost name).map fun (source, column) => .qualified source column

end Belay.Sqlite
