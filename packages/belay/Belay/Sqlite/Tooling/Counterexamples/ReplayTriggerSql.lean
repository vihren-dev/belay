import Belay.Sqlite.Tooling.Counterexamples.ReplayViewSql

set_option doc.verso true

/-! Print trigger events, conditions and body statements for catalog reconstruction.
Replay validates the reconstructed database before it reports a counterexample. -/

namespace Belay.Sqlite.Replay

open Belay.Sqlite.Model

/-- The SQL name of the conflict algorithm in a catalog definition or trigger statement. -/
def conflictSql : ConflictAlgorithm → String
  | .abort => "ABORT"
  | .fail => "FAIL"
  | .rollback => "ROLLBACK"
  | .ignore => "IGNORE"
  | .replace => "REPLACE"

/-- Look up an indexed subquery in a trigger's body statement. -/
private def bodyExpr (queries : List Syntax.Subquery) : Syntax.Expr → Option String :=
  syntaxExprSql fun index => do querySql queries (some index) (← queries[index]?) queries.length

/-- The SET assignments and optional WHERE clause of an UPDATE, including an upsert action. -/
private def updateSql (expr : Syntax.Expr → Option String) (assignments : List (Identifier × Syntax.Expr))
    (filter : Option Syntax.Expr) : Option String := do
  let pairs ← assignments.mapM fun (name, value) => do pure <| (← identifier name) ++ " = " ++ (← expr value)
  let condition ← filter.mapM expr
  return " SET " ++ String.intercalate ", " pairs ++ (condition.map (" WHERE " ++ ·)).getD ""

/-- A trigger's UPSERT clause with its target and action. -/
private def upsertSql (expr : Syntax.Expr → Option String) (clause : Syntax.ConflictClause) : Option String := do
  let columns ← clause.target.mapM columnListSql
  let action ← match clause.action with
    | .nothing => pure "DO NOTHING"
    | .update assignments condition => pure <| "DO UPDATE" ++ (← updateSql expr assignments condition)
  return " ON CONFLICT" ++ columns.getD "" ++ " " ++ action

/-- Render one statement of the trigger, retaining the subqueries of that statement. -/
private def bodySql : Syntax.BodyStatement → Option String
  | .insert table columns rows conflicts algorithm queries => do
    let expr := bodyExpr queries
    let names ← columns.mapM columnListSql
    let values ← rows.mapM fun row => do pure <| "(" ++ String.intercalate ", " (← row.mapM expr) ++ ")"
    return "INSERT" ++ (algorithm.map ((" OR " ++ ·) ∘ conflictSql)).getD "" ++ " INTO " ++
      (← identifier table) ++ names.getD "" ++ (if values.isEmpty then " DEFAULT VALUES" else
      " VALUES " ++ String.intercalate ", " values) ++ String.join (← conflicts.mapM (upsertSql expr))
  | .update table assignments condition queries => do
    return "UPDATE " ++ (← identifier table) ++ (← updateSql (bodyExpr queries) assignments condition)
  | .delete table condition queries => do
    let filter ← condition.mapM (bodyExpr queries)
    return "DELETE FROM " ++ (← identifier table) ++ (filter.map (" WHERE " ++ ·)).getD ""
  | .select columns source joins filter groupBy orderBy limit offset queries having distinct =>
    querySql queries none
      { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct }
      (queries.length + 1)

/-- Propose a CREATE TRIGGER statement with its original event, WHEN condition and body. -/
def triggerSql (name : Identifier) (trigger : CatalogTrigger) : Option String := do
  let event ← match trigger.event with
    | .insert => pure "INSERT"
    | .delete => pure "DELETE"
    | .update [] => pure "UPDATE"
    | .update columns => pure <| "UPDATE OF " ++ String.intercalate ", " (← columns.mapM identifier)
  let condition ← trigger.condition.mapM (bodyExpr [])
  let statements ← trigger.body.mapM bodySql
  let time := match trigger.time with | .before => "BEFORE" | .after => "AFTER"
  return "CREATE TRIGGER " ++ (← identifier name) ++ " " ++ time ++ " " ++ event ++ " ON " ++
    (← identifier trigger.table) ++ (condition.map (" WHEN " ++ ·)).getD "" ++ " BEGIN " ++
    String.intercalate "; " statements ++ "; END;\n"

end Belay.Sqlite.Replay
