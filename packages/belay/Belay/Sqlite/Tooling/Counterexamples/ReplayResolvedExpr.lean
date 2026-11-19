import Belay.Sqlite.Tooling.Counterexamples.ReplayFunctionNames
import Belay.Sqlite.Model.Queries.Evaluation.Calls

set_option doc.verso true

namespace Belay.Sqlite.Replay
open Belay.Sqlite.Model

/-- Render a resolved call or infix operator with its arguments. -/
private def callSql (name : String) (args : List String) : Option String := do
  if ["||", "->", "->>"].contains name then
    let [a, b] := args | none
    return binarySql name a b
  return name ++ "(" ++ String.intercalate ", " args ++ ")"

/-- A stored comparison's collation must survive reading the printed expression back. -/
private def collated (value : String) (collation : Collation) : String :=
  "(" ++ value ++ " COLLATE " ++ collation.sqlName ++ ")"

/-- A local column reference. Backticks preserve the exact spelling for later DDL diagnostics.
A double-quoted reference reproduces a catalog that recorded a non-exact name. -/
def columnReferenceSql (table : CatalogTable) (position : Nat) : Option String := do
  let name := (← table.columns[position]?).name
  let quoted ← identifier name
  if table.exactNames then
    return "`" ++ name.text.replace "`" "``" ++ "`"
  return quoted

/-- Propose SQL for an expression over one catalog table. Resolve column positions against its actual
columns. A subquery or aggregate slot has no source in a generated column, CHECK or index.
The caller checks the reconstruction against the original catalog. -/
partial def resolvedExprSql (table : CatalogTable) : Resolved.Expr → Option String
  | .column position => columnReferenceSql table position
  | .literal value => valueLiteral value
  | .compare op _ a b coll => do
    return binarySql (comparisonSql op) (collated (← resolvedExprSql table a) coll) (← resolvedExprSql table b)
  | .and a b => return binarySql "AND" (← resolvedExprSql table a) (← resolvedExprSql table b)
  | .or a b => return binarySql "OR" (← resolvedExprSql table a) (← resolvedExprSql table b)
  | .not e => return "(NOT " ++ (← resolvedExprSql table e) ++ ")"
  | .isNull e negated => return "(" ++ (← resolvedExprSql table e) ++ (if negated then " IS NOT NULL)" else " IS NULL)")
  | .arithmetic op a b => return binarySql (arithmeticSql op) (← resolvedExprSql table a) (← resolvedExprSql table b)
  | .cast affinity e => do
    let kind := match affinity with
      | .integer => "INTEGER" | .real => "REAL" | .text => "TEXT" | .blob => "BLOB" | .numeric => "NUMERIC"
    return "CAST(" ++ (← resolvedExprSql table e) ++ " AS " ++ kind ++ ")"
  | .coalesce a b => do callSql "coalesce" [← resolvedExprSql table a, ← resolvedExprSql table b]
  | .now keyword => some (match keyword with
    | .date => "CURRENT_DATE" | .time => "CURRENT_TIME" | .timestamp => "CURRENT_TIMESTAMP")
  | .parameter n => some ("?" ++ toString n)
  | .counter k => some (match k with
    | .changes => "changes()" | .totalChanges => "total_changes()" | .lastInsertRowid => "last_insert_rowid()")
  | .json f args => do callSql (jsonFunctionSql f) (← args.toList.mapM (resolvedExprSql table))
  | .date f args => do
    let name := match f with
      | .date => "date" | .time => "time" | .datetime => "datetime" | .julianday => "julianday"
      | .unixepoch => "unixepoch" | .strftime => "strftime"
    callSql name (← args.toList.mapM (resolvedExprSql table))
  | .scalar f args => do
    let rendered ← args.toList.mapM (resolvedExprSql table)
    let rendered := match f, rendered with
      | .nullif coll, a :: rest | .min coll, a :: rest | .max coll, a :: rest => collated a coll :: rest
      | _, rest => rest
    callSql (scalarFunctionSql f) rendered
  | .inList e args _ coll negated => do
    let items ← args.toList.mapM (resolvedExprSql table)
    return binarySql (if negated then "NOT IN" else "IN") (collated (← resolvedExprSql table e) coll)
      ("(" ++ String.intercalate ", " items ++ ")")
  | .exists _ | .subquery _ | .inQuery .. | .aggregateValue _ => none

end Belay.Sqlite.Replay
