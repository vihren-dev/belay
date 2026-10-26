import Belay.Sqlite.Model.Resolution.CommonTableWrites

set_option doc.verso true

/-! The projection of the traced subquery steps of a write. The steps take a traced callback for
the write itself; their projection is the untraced step with the projection of the callback. -/

namespace Belay.Sqlite.Model

/-- For every write step and traced callback: the projection of the traced step over the subqueries of
a write is {name}`resolveWriteSubqueries` with the projection of the callback. Proof sketch: unfold both
sides; the view case and the source stage have the same branches, and the callback is applied to the
same arguments. -/
@[traced_drop] theorem drop_resolveWriteSubqueriesTraced (context : ResolveContext) (catalog : Catalog)
    (field : Nat) (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : List Resolved.Query → SubqueryShapes → TracedResolution)
    (columnNames : List (Nat × List Identifier)) (viewRoots : List (Nat × Identifier)) :
    (resolveWriteSubqueriesTraced context catalog field tableName scopeOf subqueries resolveWrite columnNames
      viewRoots).drop =
    resolveWriteSubqueries context catalog field tableName scopeOf subqueries
      (fun resolved shapes => (resolveWrite resolved shapes).drop) columnNames viewRoots := by
  unfold resolveWriteSubqueries resolveWriteSubqueriesTraced resolveViewTargetTraced
  split
  · simp [traced_drop]
  · simp only [traced_drop]

/-- For every write step with its CTE and view copies and traced callback: the projection of the traced
step is {name}`resolveCommonTableWrite` with the projection of the callback. Proof sketch: unfold both
sides; the view case is the same, and the expansion and the subquery step are equal by
{name}`drop_resolveWriteSubqueriesTraced`, the trace functions leaving the result as it is. -/
@[traced_drop] theorem drop_resolveCommonTableWriteTraced (context : ResolveContext) (catalog : Catalog)
    (field : Nat) (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : (Nat → Nat) → List Resolved.Query → SubqueryShapes → TracedResolution) :
    (resolveCommonTableWriteTraced context catalog field tableName scopeOf subqueries resolveWrite).drop =
    resolveCommonTableWrite context catalog field tableName scopeOf subqueries
      (fun index resolved shapes => (resolveWrite index resolved shapes).drop) := by
  unfold resolveCommonTableWrite resolveCommonTableWriteTraced resolveViewTargetTraced
  split
  · simp only [traced_drop]
  · split
    · simp only [traced_drop]
    · simp only [traced_drop]
      split
      · rfl
      · rfl
      · congr 3
        funext resolved shapes
        split <;> rfl

/-- For every write over subqueries: {name}`resolveWriteSubqueries` is a view write
({name}`resolveViewTarget`) for a view target; else it resolves the subqueries around the scope of the
table, and the write with them, as the function did before the name trace. Proof sketch: unfold the
traced form and split on the view test and on the result of the subqueries; both sides are equal by
definition. -/
theorem resolveWriteSubqueries_arm (context : ResolveContext) (catalog : Catalog) (field : Nat)
    (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : List Resolved.Query → SubqueryShapes → StatementResolution)
    (columnNames : List (Nat × List Identifier)) (viewRoots : List (Nat × Identifier)) :
    resolveWriteSubqueries context catalog field tableName scopeOf subqueries resolveWrite columnNames viewRoots =
      if (catalog.findView tableName).isSome then resolveViewTarget context catalog tableName (resolveWrite [] {}) else
      match resolveSubqueries context.profile.dqsDml catalog field
          (QueryScope.ofScope (((catalog.findTable tableName).map
            fun (position, table) => (scopeOf table).withTablePosition position).getD []))
          subqueries columnNames viewRoots with
      | .error (.noSuchTable name) => prepareError catalog (.noSuchTable name)
      | .error (.value issue) => issueResolution catalog [] issue
      | .ok (resolved, shapes) =>
        if (catalog.findTable tableName).any fun (position, _) => resolved.any (·.readsTable position) then
          restrict [field] .subqueryReadsTarget
        else resolveWrite resolved { later := shapes } := by
  unfold resolveWriteSubqueries resolveWriteSubqueriesTraced resolveViewTargetTraced
  split
  · simp only [traced_drop]
  · simp only [traced_drop, resolveSubqueries]
    split <;> simp_all

/-- For every write over CTEs and views: {name}`resolveCommonTableWrite` is a view write for a view
target; else, with no copies needed, {name}`resolveWriteSubqueries`; else it expands the definitions and
resolves the write over the copies, with the paths of the issues moved back to the written statement, as
the function did before the name trace. Proof sketch: unfold the traced form and split on the two tests
and on the expansion; the callbacks agree by {name}`drop_resolveWriteSubqueriesTraced`. -/
theorem resolveCommonTableWrite_arm (context : ResolveContext) (catalog : Catalog) (field : Nat)
    (tableName : Identifier) (scopeOf : CatalogTable → Scope) (subqueries : List Syntax.Subquery)
    (resolveWrite : (Nat → Nat) → List Resolved.Query → SubqueryShapes → StatementResolution) :
    resolveCommonTableWrite context catalog field tableName scopeOf subqueries resolveWrite =
      if (catalog.findView tableName).isSome then resolveViewTarget context catalog tableName (resolveWrite id [] {}) else
      if !querySourceCopiesNeeded catalog commonTablePlaceholder subqueries then
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
              | none => resolveWrite index resolved shapes) expanded.copies.columnNames
              expanded.copies.viewRoots).mapError fun issue =>
              { issue with path := expanded.copies.originalPath field issue.path } := by
  unfold resolveCommonTableWrite resolveCommonTableWriteTraced resolveViewTargetTraced
  split
  · simp only [traced_drop]
  · split
    · simp only [traced_drop]
    · simp only [traced_drop, expandCommonTables]
      split <;> try simp_all
      all_goals first | rfl | (congr 2; funext resolved shapes; split <;> simp_all [traced_drop])

end Belay.Sqlite.Model
