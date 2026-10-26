import Belay.Sqlite.Model.Resolution.Writes
import Belay.Sqlite.Model.Resolution.WriteStages

set_option doc.verso true

/-! Resolution of DELETE (ADR 0012, amendment 1, slice 3c): the {lit}`WHERE` filter is a
condition, resolved as in {lit}`SELECT`, and the {lit}`RETURNING` columns are resolved
over the table's columns. -/

namespace Belay.Sqlite.Model

/-- Resolve DELETE. Path 1 is the filter and path {name}`deleteReturningField` the
{lit}`RETURNING` columns. SQLite's own tables are a model restriction, as in
{lit}`SELECT`. The filter may name the statement's resolved subqueries, whose shapes are
{lit}`shapes`. In a trigger's body, the filter also sees the trigger's rows {lit}`trigger`,
after the table's cells (ADR 0018, D5). A view target is {name}`resolveViewModify`. The trace holds
the table at path 0, then the names of the filter and of the {lit}`RETURNING` columns. -/
def resolveDeleteTraced (context : ResolveContext) (catalog : Catalog) (tableName : Identifier)
    (filter : Option Syntax.Expr) (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query)
    (shapes : SubqueryShapes) (trigger : Option TriggerRow := none) : TracedResolution :=
  let dqs := context.profile.dqsDml
  Traced.withTarget catalog tableName true (Traced.lift (resolveViewModify catalog tableName))
    (if reservedName tableName then Traced.lift (restrict [0] .systemTable)
      else Traced.lift (prepareError catalog (.noSuchTable tableName))) fun position table =>
  let scope := Scope.singleAt (some position) tableName table.columns !table.withoutRowid
  Traced.stage catalog [1] (resolveWriteFilterTraced dqs
      (scope ++ (trigger.map (·.scope table.columns.length)).getD []) shapes filter) fun resolvedFilter =>
  Traced.stage catalog [deleteReturningField] (resolveReturningTraced dqs scope returning) fun columns =>
  Traced.ok (.delete position resolvedFilter columns subqueries, catalog)

/-- The resolution of a DELETE: {name}`resolveDeleteTraced` without its trace. -/
def resolveDelete (context : ResolveContext) (catalog : Catalog) (tableName : Identifier)
    (filter : Option Syntax.Expr) (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query)
    (shapes : SubqueryShapes) (trigger : Option TriggerRow := none) : StatementResolution :=
  (resolveDeleteTraced context catalog tableName filter returning subqueries shapes trigger).drop

end Belay.Sqlite.Model
