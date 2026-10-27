import Belay.Sqlite.Model.Resolution.RewriteExpr

set_option doc.verso true

/-! Replace one name of a query by its node path (ADR 0019, D4), with the paths of the name trace
({lit}`resolveSelectTraced`): the result columns are the child 0, and the expression of the column
{lit}`i` is {lit}`[0, i, 0]`; the first source is the child 1; the join {lit}`i` is {lit}`[2, i]`, with its source
at 1, its {lit}`ON` condition at 2 and the name {lit}`k` of its {lit}`USING` at {lit}`[3, k]`; then the filter 3,
the terms of {lit}`GROUP BY` {lit}`[4, k]`, the terms of {lit}`ORDER BY` {lit}`[5, i, 0]`, the limit 6, the offset 7 and
{lit}`HAVING` 9. The table of a reference is its child 0. The subqueries of a statement are
addressed by their index, below the child 8 of the statement, and are not part of a query. -/

namespace Belay.Sqlite.Model.Syntax

/-- The reference with the name of its table replaced, when the path is the table of a named
reference (a derived source and a function have no table to rename). -/
def TableReference.renameAt (edit : NameEdit) : List Nat → TableReference → Option TableReference
  | [0], reference =>
    if reference.query.isSome || reference.arguments.isSome then none
    else (edit.replace? reference.table).map fun table => { reference with table }
  | _, _ => none

/-- The result column with the name at the path replaced: a name in the expression of the column,
or the qualifier of {lit}`source.*`. The text of the column is rewritten apart from this
({lit}`SourceText.renameAt`). -/
def ResultColumn.renameAt (edit : NameEdit) : List Nat → ResultColumn → Option ResultColumn
  | 0 :: rest, .expression value alias text => (value.renameAt edit rest).map (.expression · alias text)
  | [0], .sourceStar source => (edit.replace? source).map .sourceStar
  | _, .star | _, .sourceStar _ | _, .expression .. => none

/-- The join with the name at the path replaced: in its source, its condition or its {lit}`USING`
list. -/
def Join.renameAt (edit : NameEdit) : List Nat → Join → Option Join
  | 1 :: rest, join => (join.source.renameAt edit rest).map ({ join with source := · })
  | 2 :: rest, join => do
    let condition ← join.condition
    let renamed ← condition.renameAt edit rest
    pure { join with condition := some renamed }
  | [3, index], join => do
    let names ← join.usingColumns
    let renamed ← replaceNth? edit.replace? index names
    pure { join with usingColumns := some renamed }
  | _, _ => none

/-- The query with the name at the path replaced, or none when the path leads to no name of it, or to
a name other than the old name of the edit. -/
def Subquery.renameAt (edit : NameEdit) : List Nat → Subquery → Option Subquery
  | 0 :: index :: rest, query => do
    let columns ← replaceNth? (ResultColumn.renameAt edit rest) index query.columns
    pure { query with columns }
  | 1 :: rest, query => do
    let source ← query.source
    let renamed ← source.renameAt edit rest
    pure { query with source := some renamed }
  | 2 :: index :: rest, query => do
    let joins ← replaceNth? (Join.renameAt edit rest) index query.joins
    pure { query with joins }
  | 3 :: rest, query => do
    let filter ← query.filter
    let renamed ← filter.renameAt edit rest
    pure { query with filter := some renamed }
  | 4 :: index :: rest, query => do
    let groupBy ← replaceNth? (Expr.renameAt edit rest) index query.groupBy
    pure { query with groupBy }
  | 5 :: index :: 0 :: rest, query => do
    let orderBy ← replaceNth? (fun term => (term.expression.renameAt edit rest).map ({ term with expression := · })) index
      query.orderBy
    pure { query with orderBy }
  | 6 :: rest, query => do
    let limit ← query.limit
    let renamed ← limit.renameAt edit rest
    pure { query with limit := some renamed }
  | 7 :: rest, query => do
    let offset ← query.offset
    let renamed ← offset.renameAt edit rest
    pure { query with offset := some renamed }
  | 9 :: rest, query => do
    let having ← query.having
    let renamed ← having.renameAt edit rest
    pure { query with having := some renamed }
  | _, _ => none

end Belay.Sqlite.Model.Syntax
