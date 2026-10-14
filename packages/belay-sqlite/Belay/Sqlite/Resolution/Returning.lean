import Belay.Sqlite.Resolution.QueryExprs

set_option doc.verso true

/-! Resolution of the {lit}`RETURNING` columns of an INSERT or UPDATE (ADR 0012,
slice 3a). SQLite resolves them as the result columns of a {lit}`SELECT` over the
written table, after the values and the filter: {lit}`*` is every column under its
defined name, an expression is evaluated over the written row and named by its
alias, the defined name of a bare column, or its source text. An aggregate is
SQLite's {lit}`misuse of aggregate function`. -/

namespace Belay.Sqlite

/-- The defined name of the column that a bare result expression names, as SQLite names
a result column without an alias: the column's name as declared, for an unqualified name
of one column or a qualified name; none for any other expression. -/
def definedName (scope : Scope) : Syntax.Expr → Option String
  | .identifier name _ => match scope.matches name with
    | [position] => scope.columns[position]?.map CatalogColumn.name
    | [] | _ :: _ :: _ => none
  | .qualified source column => (scope.qualified source column).bind (scope.columns[·]?.map CatalogColumn.name)
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .negate _ | .positive _ | .equals ..
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic ..
  | .cast .. | .callPair .. => none

/-- The columns of {lit}`source.*` with their positions in the concatenated row and their
names, or SQLite's {lit}`no such table: source` when no source has the name. -/
def sourceStarColumns (scope : Scope) (source : String) : Except ValueIssue (List (Resolved.Expr × String)) :=
  match scope.source? source with
  | some (offset, columns) => .ok (columns.mapIdx fun position column => (.column (offset + position), column.name))
  | none => .error (.prepare (.noSuchSource source))

/-- One {lit}`RETURNING` column at position {lit}`item`: the expressions and names it
gives. The paths of its issues start at the column's position. -/
def returningColumn (dqs : Bool) (scope : Scope) (item : Nat) :
    Syntax.ResultColumn → Except ValueIssue (List (Resolved.Expr × String))
  | .star => .ok (scope.columns.mapIdx fun position column => (.column position, column.name))
  | .sourceStar source => sourceStarColumns scope source
  | .expression value alias text => do
      let (resolved, _) ← (resolveOperand dqs scope true value).mapError (·.under [item, 0])
      .ok [(resolved, alias.getD ((definedName scope value).getD text))]

/-- The {lit}`RETURNING` columns of a write over the table's scope, in order, or the
first issue. No {lit}`RETURNING` is the empty list. -/
def resolveReturning (dqs : Bool) (scope : Scope) (items : List Syntax.ResultColumn) :
    Except ValueIssue (List (Resolved.Expr × String)) :=
  (items.mapIdx fun item column => returningColumn dqs scope item column).foldr
    (fun next rest => do let first ← next; let others ← rest; .ok (first ++ others)) (.ok [])

end Belay.Sqlite
