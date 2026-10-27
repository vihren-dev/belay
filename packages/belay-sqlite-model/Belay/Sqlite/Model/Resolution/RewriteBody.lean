import Belay.Sqlite.Model.Resolution.RewriteSelect
import Belay.Sqlite.Model.Resolution.Triggers

set_option doc.verso true

/-! Replace one name of a statement of a trigger's body, and of the trigger itself (ADR 0019, D4), by
the paths of {lit}`resolveProgramTraced`. A statement has the fields of the statement of the same name
({lit}`Statement.insert`, {lit}`Statement.update`, {lit}`Statement.delete` and {lit}`Statement.select`): the
table of a write is the child 0; of an INSERT the column {lit}`k` of the list is {lit}`[1, k]`, the cell {lit}`c`
of the row {lit}`r` is {lit}`[2, r, c]` and the subqueries are below the child 6; of an UPDATE the assignment
{lit}`k` has its target at {lit}`[1, k, 0]` and its value at {lit}`[1, k, 1]`, the filter is the child 2 and the
subqueries are below the child 4; of a DELETE the filter is the child 1 and the subqueries are below the
child 3. A SELECT has the paths of a query of a statement. -/

namespace Belay.Sqlite.Model.Syntax

/-- The statement of a body with the name at the path replaced; the path is below the statement. -/
def BodyStatement.renameAt (edit : NameEdit) : List Nat → BodyStatement → Option BodyStatement
  | [0], .insert table columns rows conflicts algorithm subqueries =>
    (edit.replace? table).map (.insert · columns rows conflicts algorithm subqueries)
  | [1, index], .insert table columns rows conflicts algorithm subqueries => do
    let names ← columns
    let renamed ← replaceNth? edit.replace? index names
    pure (.insert table (some renamed) rows conflicts algorithm subqueries)
  | 2 :: row :: cell :: rest, .insert table columns rows conflicts algorithm subqueries => do
    let renamed ← replaceNth? (fun cells => replaceNth? (Expr.renameAt edit rest) cell cells) row rows
    pure (.insert table columns renamed conflicts algorithm subqueries)
  | 6 :: index :: rest, .insert table columns rows conflicts algorithm subqueries => do
    let renamed ← replaceNth? (Subquery.renameAt edit rest) index subqueries
    pure (.insert table columns rows conflicts algorithm renamed)
  | [0], .update table assignments filter subqueries =>
    (edit.replace? table).map (.update · assignments filter subqueries)
  | [1, index, 0], .update table assignments filter subqueries => do
    let renamed ← replaceNth? (fun (name, value) => (edit.replace? name).map (·, value)) index assignments
    pure (.update table renamed filter subqueries)
  | 1 :: index :: 1 :: rest, .update table assignments filter subqueries => do
    let renamed ← replaceNth? (fun (name, value) => (value.renameAt edit rest).map (name, ·)) index assignments
    pure (.update table renamed filter subqueries)
  | 2 :: rest, .update table assignments filter subqueries => do
    let renamed ← (← filter).renameAt edit rest
    pure (.update table assignments (some renamed) subqueries)
  | 4 :: index :: rest, .update table assignments filter subqueries => do
    let renamed ← replaceNth? (Subquery.renameAt edit rest) index subqueries
    pure (.update table assignments filter renamed)
  | [0], .delete table filter subqueries => (edit.replace? table).map (.delete · filter subqueries)
  | 1 :: rest, .delete table filter subqueries => do
    let renamed ← (← filter).renameAt edit rest
    pure (.delete table (some renamed) subqueries)
  | 3 :: index :: rest, .delete table filter subqueries => do
    let renamed ← replaceNth? (Subquery.renameAt edit rest) index subqueries
    pure (.delete table filter renamed)
  | path, .select columns source joins filter groupBy orderBy limit offset subqueries having distinct => do
    let query : Subquery := { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none,
                              having, distinct }
    let (renamed, subqueries) ← renameSelectAt { edit with path } query subqueries
    pure (.select renamed.columns renamed.source renamed.joins renamed.filter renamed.groupBy renamed.orderBy
      renamed.limit renamed.offset subqueries renamed.having renamed.distinct)
  | _, _ => none

end Belay.Sqlite.Model.Syntax

namespace Belay.Sqlite.Model

open Syntax

/-- The trigger with the name at the path replaced, as {lit}`resolveProgramTraced` places the names: the
{lit}`WHEN` condition is the child 5 and the statement {lit}`k` of the body is {lit}`[6, k]`. The table and the
columns of {lit}`UPDATE OF` are names of the catalog and are not part of the program; a rename decides
them apart. -/
def CatalogTrigger.renameAt (edit : NameEdit) : List Nat → CatalogTrigger → Option CatalogTrigger
  | 5 :: rest, trigger => do
    let renamed ← (← trigger.condition).renameAt edit rest
    pure { trigger with condition := some renamed }
  | 6 :: index :: rest, trigger => do
    let body ← replaceNth? (BodyStatement.renameAt edit rest) index trigger.body
    pure { trigger with body }
  | _, _ => none

end Belay.Sqlite.Model
