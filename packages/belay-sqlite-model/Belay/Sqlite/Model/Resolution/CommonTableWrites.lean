import Belay.Sqlite.Model.Resolution.WriteResolution
import Belay.Sqlite.Model.Resolution.CommonTableExpansion

set_option doc.verso true

/-! WITH on the supported VALUES INSERT, UPDATE and DELETE forms. Expansion changes
only the indexed query list and the expressions that refer to it; ordinary write resolution
still checks the target, row rules and subqueries that read their own write target. -/

namespace Belay.Sqlite.Model

/-- Resolve a write after instantiating its used CTEs. The callback receives the index
mapping for its VALUES, SET and WHERE expressions, then the same resolved queries and
shapes as {name}`resolveWriteSubqueries`. With no definitions the mapping is identity.
An unexpanded view target is restricted before a CTE body can determine a competing error. -/
def resolveCommonTableWrite (context : ResolveContext) (catalog : Catalog) (field : Nat)
    (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : (Nat → Nat) → List Resolved.Query → SubqueryShapes → StatementResolution) : StatementResolution :=
  if (catalog.findView tableName).isSome then restrict [0] .subqueryHere else
  if !subqueries.any (·.commonTable.isSome) then
    resolveWriteSubqueries context catalog field tableName scopeOf subqueries (resolveWrite id)
  else match expandCommonTables catalog field commonTablePlaceholder subqueries with
    | .error (.noSuchTable name) => prepareError catalog (.noSuchTable name)
    | .error (.value issue) => issueResolution catalog [] issue
    | .ok expanded =>
      let index := fun original => (expanded.rootIndexes.lookup original).getD
        (expanded.copies.queries.size + original)
      (resolveWriteSubqueries context catalog field tableName scopeOf expanded.copies.queries.toList
        (fun resolved shapes => match expanded.copies.recursionIssue field resolved with
          | some issue => issueResolution catalog [] issue
          | none => resolveWrite index resolved shapes) expanded.copies.columnNames).mapError fun issue =>
          { issue with path := expanded.copies.originalPath field issue.path }

end Belay.Sqlite.Model
