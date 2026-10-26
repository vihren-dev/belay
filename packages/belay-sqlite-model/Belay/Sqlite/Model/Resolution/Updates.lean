import Belay.Sqlite.Model.Resolution.Writes
import Belay.Sqlite.Model.Resolution.WriteStages

set_option doc.verso true

/-! Resolution of UPDATE (ADR 0012, amendment 1, "Resolved forms"): each {lit}`SET`
value is an expression over the table's columns, and the {lit}`WHERE` filter is a
condition, both resolved as in {lit}`SELECT`. A value that names no column folds to
the literal of its stored value. A value that reads the row may not assign a column of
a unique key: that is a model restriction. -/

namespace Belay.Sqlite.Model

/-- Resolve UPDATE. Path 1 is the assignment list, path 2 the filter and path 3 the
{lit}`RETURNING` columns, which resolve last. The assignments resolve in order, then
the filter as a condition; then a column assigned twice is a model restriction. A
{lit}`SET` value that reads the row for a key column is the restriction
{name}`RestrictionKind.rowDependentKey` of its assignment. A table with a constraint
algorithm other than ABORT is {name}`RestrictionKind.constraintAlgorithmUpdate`, after
every other check. The values and the filter may name the statement's resolved subqueries,
whose shapes are {lit}`shapes`. In a trigger's body, the values and the filter also see the
trigger's rows {lit}`trigger`, after the table's cells (ADR 0018, D5). A view target is {name}`resolveViewModify`.
The trace holds the table at path 0, then the names of the assignments, the filter and the
{lit}`RETURNING` columns, in the order in which the resolver reaches them. -/
def resolveUpdateTraced (context : ResolveContext) (catalog : Catalog) (tableName : Identifier)
    (assignments : List (Identifier × Syntax.Expr)) (filter : Option Syntax.Expr)
    (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query) (shapes : SubqueryShapes)
    (trigger : Option TriggerRow := none) : TracedResolution :=
  let dqs := context.profile.dqsDml
  Traced.withTarget catalog tableName false (Traced.lift (resolveViewModify catalog tableName))
    (Traced.lift (prepareError catalog (.noSuchTable tableName))) fun position table =>
  let keys := catalog.uniqueKeys position table
  let scope := Scope.singleAt (some position) tableName table.columns !table.withoutRowid
  let around := (trigger.map (·.scope table.columns.length)).getD []
  Traced.stage catalog [1] (resolveAllTraced (fun item => resolveAssignmentTraced dqs scope shapes
      (keys.flatMap (·.reads table.columns.length)) (fun name => .prepare (.updateGenerated name))
      (if table.withoutRowid then none else some table.rowidAlias) item around) assignments) fun resolved =>
  Traced.stage catalog [2] (resolveWriteFilterTraced dqs (scope ++ around) shapes filter) fun resolvedFilter =>
  let positions := resolved.map Prod.fst
  if positions.eraseDups.length != positions.length then Traced.lift (restrict [1] .updateColumnTwice)
  else Traced.stage catalog [updateReturningField] (resolveReturningTraced dqs scope returning) fun columns =>
    if (catalog.keyAlgorithms position table).all (· == .abort) &&
        table.columns.all (·.notNullAlgorithm == .abort) then
      Traced.ok (.update position resolved resolvedFilter columns subqueries, catalog)
    else Traced.lift (restrict [] .constraintAlgorithmUpdate)

/-- The resolution of an UPDATE: {name}`resolveUpdateTraced` without its trace. -/
def resolveUpdate (context : ResolveContext) (catalog : Catalog) (tableName : Identifier)
    (assignments : List (Identifier × Syntax.Expr)) (filter : Option Syntax.Expr)
    (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query) (shapes : SubqueryShapes)
    (trigger : Option TriggerRow := none) : StatementResolution :=
  (resolveUpdateTraced context catalog tableName assignments filter returning subqueries shapes trigger).drop

end Belay.Sqlite.Model
