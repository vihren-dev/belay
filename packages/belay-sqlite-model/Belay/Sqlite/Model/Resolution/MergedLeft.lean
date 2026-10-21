import Belay.Sqlite.Model.Resolution.Values
import Belay.Sqlite.Model.Resolution.ScopeNames
import Belay.Sqlite.Model.Resolution.Syntax
import Belay.Sqlite.Model.Resolution.MergedNames

set_option doc.verso true

/-! The left side of the equality of a {lit}`USING` or {lit}`NATURAL` join (ADR 0012,
amendments 2 and 3; ADR 0013, D5). Without right and full joins in the {lit}`FROM`, it is the left-most
left column of the name (slice 4b). With one anywhere, also after the join, SQLite
compares the coalesce of every left column of the name, and requires every left table
after the first with the name to merge it by its own join, else
{lit}`ambiguous reference to a in USING()` (slice 4d, checked on native 3.51.0). -/

namespace Belay.Sqlite.Model

/-- Every column of the folded name in the scope, in order: the source's name, the
column's name as declared, and whether the source's join merged it. -/
def Scope.namedColumns (scope : Scope) (name : Identifier) : List (Identifier × Identifier × Bool) :=
  scope.filterMap fun source => (columnPosition source.columns name).bind fun index =>
    source.columns[index]?.map fun column => (source.name, column.name, source.merged.contains index)

/-- A merged name, as written, when every left column of the name after the first is
merged by its own source's join; else SQLite's
{name}`ExprError.ambiguousUsingReference`. SQLite checks it when the {lit}`FROM` has a
right or full join. -/
def usingReferenceChecked (left : Scope) (name : Identifier) : Except ValueIssue Identifier :=
  if ((left.namedColumns name).drop 1).all (·.2.2) then .ok name
  else .error (.prepare (.ambiguousUsingReference name))

/-- The positions in the joined row of the scope of every column of the folded name, in
order. -/
def Scope.namedPositions (scope : Scope) (name : Identifier) : List Nat :=
  scope.flatMap fun source => ((columnPosition source.columns name).map (source.offset + ·)).toList

/-- Whether a source of the scope has a column of the folded name. -/
def Scope.hasColumn (scope : Scope) (name : Identifier) : Bool :=
  !(scope.namedPositions name).isEmpty

/-- The left side of the equality of a merged name, resolved, with its affinity
({name}`Scope.nameOperand`): with {lit}`coalesced` (a right or full join in the
{lit}`FROM`), every left column of the name, so their coalesce when there are several;
else the left-most left column. None when the left input has no column of the name. -/
def mergedLeft (coalesced : Bool) (left : Scope) (name : Identifier) : Option Operand :=
  match left.namedPositions name with
  | [] => none
  | first :: rest => some (left.nameOperand (if coalesced then first :: rest else [first]))

/-- The collation of the equality of a merged name: that of the left-most left column of
the name, BINARY when the left input has none. SQLite gives a coalesce of the left
columns the collation of its first argument, and a column always has a collation, so the
column of the joined source never decides it (checked on native 3.51.0). -/
def Scope.namedCollation (scope : Scope) (name : Identifier) : Collation :=
  ((scope.find? fun source => (columnPosition source.columns name).isSome).bind fun source =>
    (columnPosition source.columns name).bind fun index => source.columns[index]?.map (·.collation)).getD .binary

end Belay.Sqlite.Model
