import Belay.Sqlite.Tooling.Counterexamples.ReplaySyntaxExpr

set_option doc.verso true

/-! Print stored SELECT bodies and their indexed subqueries for view reconstruction.
Replay validates the reconstructed database before it reports a counterexample. -/

namespace Belay.Sqlite.Replay

open Belay.Sqlite.Model

/-- A comma-separated list of quoted column names, with parentheses. -/
def columnListSql (columns : List Identifier) : Option String := do
  return "(" ++ String.intercalate ", " (← columns.mapM identifier) ++ ")"

/-- The optional AS alias of a table or result column. -/
private def aliasSql (alias : Option Identifier) : Option String := do
  let name ← alias.mapM identifier
  return (name.map (" AS " ++ ·)).getD ""

/-- Render a source, including its optional schema, subquery, function arguments and alias. -/
private def sourceSql (query : Nat → Option String) (source : Syntax.TableReference) : Option String := do
  let name ← match source.query with
    | some index => pure <| "(" ++ (← query index) ++ ")"
    | none => do
      let schema ← source.schema.mapM identifier
      let args ← source.arguments.mapM (List.mapM (syntaxExprSql query))
      pure <| (schema.map (· ++ ".")).getD "" ++ (← identifier source.table) ++
        (args.map fun items => "(" ++ String.intercalate ", " items ++ ")").getD ""
  return name ++ (← aliasSql source.alias)

/-- Render one result column. Preserve the original expression text when available because
SQLite also uses it as the column name. -/
private def resultSql (query : Nat → Option String) : Syntax.ResultColumn → Option String
  | .star => some "*"
  | .sourceStar name => return (← identifier name) ++ ".*"
  | .expression expr alias source => do
    let value ← if source.text.isEmpty then syntaxExprSql query expr else pure source.text
    return value ++ (← aliasSql alias)

/-- Append an optional clause whose contents have already been rendered. -/
private def clauseSql (keyword : String) (contents : Option String) : String :=
  (contents.map ((" " ++ keyword ++ " ") ++ ·)).getD ""

/-- The query body and its ordering, using the supplied lookup for nested SELECTs. -/
private def selectSql (query : Nat → Option String) (body : Syntax.Subquery) : Option String := do
  let expr := syntaxExprSql query
  let main ← match body.compound with
    | some compound => do
      let parts ← compound.rest.mapM fun (op, index) => do
        let keyword := match op with
          | .unionAll => "UNION ALL" | .union => "UNION" | .intersect => "INTERSECT" | .except => "EXCEPT"
        return keyword ++ " " ++ (← query index)
      pure <| String.intercalate " " ((← query compound.first) :: parts)
    | none => do
      let mut sql := "SELECT " ++ (if body.distinct then "DISTINCT " else "") ++
        String.intercalate ", " (← body.columns.mapM (resultSql query))
      sql := sql ++ clauseSql "FROM" (← body.source.mapM (sourceSql query))
      for join in body.joins do
        let words := join.operator ++ ["JOIN", ← sourceSql query join.source]
        sql := sql ++ " " ++ String.intercalate " " words ++ clauseSql "ON" (← join.condition.mapM expr) ++
          clauseSql "USING" (← join.usingColumns.mapM columnListSql)
      sql := sql ++ clauseSql "WHERE" (← body.filter.mapM expr)
      unless body.groupBy.isEmpty do
        sql := sql ++ " GROUP BY " ++ String.intercalate ", " (← body.groupBy.mapM expr)
      pure <| sql ++ clauseSql "HAVING" (← body.having.mapM expr)
  let order ← body.orderBy.mapM fun term => do
    return (← expr term.expression) ++ (if term.descending then " DESC" else "")
  return main ++ (if order.isEmpty then "" else " ORDER BY " ++ String.intercalate ", " order) ++
    clauseSql "LIMIT" (← body.limit.mapM expr) ++ clauseSql "OFFSET" (← body.offset.mapM expr)

/-- Rebuild a SELECT and the WITH definitions declared in its scope. Each descent consumes
one unit of fuel so a cyclic index in a computed catalog cannot loop. -/
def querySql (queries : List Syntax.Subquery) (parent : Option Nat) (body : Syntax.Subquery) :
    Nat → Option String
  | 0 => none
  | fuel + 1 => do
    let nested := fun index => do querySql queries (some index) (← queries[index]?) fuel
    let mut definitions := []
    for (item, index) in queries.zipIdx do
      if item.parent == parent then
        if let some common := item.commonTable then
          let columns ← common.columns.mapM columnListSql
          definitions := ((← identifier common.name) ++ columns.getD "" ++ " AS (" ++ (← nested index) ++ ")") :: definitions
    let withClause := if definitions.isEmpty then "" else "WITH " ++ String.intercalate ", " definitions.reverse ++ " "
    return withClause ++ (← selectSql nested body)

/-- Propose a CREATE VIEW statement from its catalog entry, including explicit output names
and nested queries. Reconstruction validates the stored expression text and positions. -/
def viewSql (name : Identifier) (view : CatalogView) : Option String := do
  let columns ← view.columns.mapM columnListSql
  return "CREATE VIEW " ++ (← identifier name) ++ columns.getD "" ++ " AS " ++
    (← querySql view.subqueries none view.query (view.subqueries.length + 1)) ++ ";\n"

end Belay.Sqlite.Replay
