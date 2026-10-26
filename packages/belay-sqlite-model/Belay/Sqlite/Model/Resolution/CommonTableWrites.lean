import Belay.Sqlite.Model.Resolution.WriteResolution
import Belay.Sqlite.Model.Resolution.QuerySourceExpansion

set_option doc.verso true

/-! CTE and view sources in the supported VALUES INSERT, UPDATE and DELETE forms. Expansion changes
only the indexed query list and the expressions that refer to it; ordinary write resolution
still checks the target, row rules and subqueries that read their own write target. -/

namespace Belay.Sqlite.Model

/-- Resolve a write after instantiating its used CTEs and view sources. The callback receives the index
mapping for its VALUES, SET and WHERE expressions, then the same resolved queries and
shapes as {name}`resolveWriteSubqueriesTraced`. With no needed copies the mapping is identity.
A view target is not writable: the write reports that error ({name}`resolveViewTarget`) before the
body of any source can give an error. The names of a copy of a {lit}`WITH` definition or a stored view
move to the written statement ({name}`CommonTableCopies.originalOccurrence`). -/
def resolveCommonTableWriteTraced (context : ResolveContext) (catalog : Catalog) (field : Nat)
    (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : (Nat → Nat) → List Resolved.Query → SubqueryShapes → TracedResolution) : TracedResolution :=
  if (catalog.findView tableName).isSome then resolveViewTargetTraced context catalog tableName (resolveWrite id [] {}) else
  if !querySourceCopiesNeeded catalog commonTablePlaceholder subqueries then
    resolveWriteSubqueriesTraced context catalog field tableName scopeOf subqueries (resolveWrite id)
  else Traced.sourceStage catalog (expandCommonTablesTraced catalog field commonTablePlaceholder subqueries)
    fun expanded =>
      let index := fun original => (expanded.rootIndexes.lookup original).getD
        (expanded.copies.queries.size + original)
      ((resolveWriteSubqueriesTraced context catalog field tableName scopeOf expanded.copies.queries.toList
        (fun resolved shapes => match expanded.copies.recursionIssue field resolved with
          | some issue => Traced.lift (issueResolution catalog [] issue)
          | none => resolveWrite index resolved shapes) expanded.copies.columnNames
          expanded.copies.viewRoots).mapError fun issue =>
          { issue with path := expanded.copies.originalPath field issue.path }).mapOccurrences
        (expanded.copies.originalOccurrence field)

/-- Resolve a write after instantiating its used CTEs and view sources:
{name}`resolveCommonTableWriteTraced` without its trace. -/
def resolveCommonTableWrite (context : ResolveContext) (catalog : Catalog) (field : Nat)
    (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : (Nat → Nat) → List Resolved.Query → SubqueryShapes → StatementResolution) : StatementResolution :=
  (resolveCommonTableWriteTraced context catalog field tableName scopeOf subqueries
    (fun index resolved shapes => Traced.lift (resolveWrite index resolved shapes))).drop

end Belay.Sqlite.Model
