import Belay.Sqlite.Model.Resolution.RewriteText

set_option doc.verso true

/-! Replace one name of a {lit}`SELECT` with its subqueries (ADR 0019, D4), as the name trace of
{lit}`resolveSelectTraced` places it: a path that starts with {lit}`[8, k]` is in the subquery {lit}`k` of the
statement, and any other path is in the query of the statement. The text of the result columns, which
names the columns of a stored view, is rewritten with the edit. -/

namespace Belay.Sqlite.Model.Syntax

/-- The result column with the name tokens of its text at the path of the edit rewritten; {lit}`column` is
the path of its expression. -/
def ResultColumn.renameText (edit : NameEdit) (column : List Nat) : ResultColumn → Option ResultColumn
  | .expression value alias text => (text.renameAt edit column).map (.expression value alias)
  | .star => some .star
  | .sourceStar source => some (.sourceStar source)

/-- The query with the text of all its result columns rewritten; {lit}`prefix_` is the path of the query:
empty for the query of the statement, {lit}`[8, k]` for the subquery {lit}`k`. -/
def Subquery.renameTexts (edit : NameEdit) (prefix_ : List Nat) (query : Subquery) : Option Subquery := do
  let columns ← query.columns.zipIdx.mapM fun (column, index) => column.renameText edit (prefix_ ++ [0, index, 0])
  pure { query with columns }

/-- The query and the subqueries of a statement with the name of the edit replaced: the name at the
path, and the name tokens of the texts of the result columns. None when the path leads to no name, or to a
name other than the old name of the edit. -/
def renameSelectAt (edit : NameEdit) (query : Subquery) (subqueries : List Subquery) :
    Option (Subquery × List Subquery) := do
  let (query, subqueries) ← match edit.path with
    | 8 :: index :: rest => do
      let renamed ← replaceNth? (Subquery.renameAt edit rest) index subqueries
      pure (query, renamed)
    | path => do pure (← query.renameAt edit path, subqueries)
  let query ← query.renameTexts edit []
  let subqueries ← subqueries.zipIdx.mapM fun (inner, index) => inner.renameTexts edit [8, index]
  pure (query, subqueries)

end Belay.Sqlite.Model.Syntax
