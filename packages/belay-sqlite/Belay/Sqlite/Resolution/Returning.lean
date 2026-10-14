import Belay.Sqlite.Resolution.QueryExprs

set_option doc.verso true

/-! Resolution of the {lit}`RETURNING` columns of an INSERT or UPDATE (ADR 0012,
slice 3a). SQLite resolves them as the result columns of a {lit}`SELECT` over the
written table, after the values and the filter: {lit}`*` is every column under its
defined name, an expression is evaluated over the written row and named by its
alias, the defined name of a bare column, or its source text. An aggregate is
SQLite's {lit}`misuse of aggregate function`. -/

namespace Belay.Sqlite

/-- One {lit}`RETURNING` column at position {lit}`item`: the expressions and names it
gives. The paths of its issues start at the column's position. -/
def returningColumn (dqs : Bool) (columns : List CatalogColumn) (item : Nat) :
    Syntax.ResultColumn → Except ValueIssue (List (Resolved.Expr × String))
  | .star => .ok (columns.mapIdx fun position column => (.column position, column.name))
  | .expression value alias text => do
      let (resolved, _) ← (resolveOperand dqs columns true value).mapError (·.under [item, 0])
      let defined := match value with
        | .identifier name _ => (columnPosition columns name).bind (columns[·]?.map CatalogColumn.name)
        | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .negate _ | .positive _ | .equals ..
        | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic ..
        | .cast .. | .callPair .. => none
      .ok [(resolved, alias.getD (defined.getD text))]

/-- The {lit}`RETURNING` columns of a write over the table's columns, in order, or the
first issue. No {lit}`RETURNING` is the empty list. -/
def resolveReturning (dqs : Bool) (columns : List CatalogColumn) (items : List Syntax.ResultColumn) :
    Except ValueIssue (List (Resolved.Expr × String)) :=
  (items.mapIdx fun item column => returningColumn dqs columns item column).foldr
    (fun next rest => do let first ← next; let others ← rest; .ok (first ++ others)) (.ok [])

end Belay.Sqlite
