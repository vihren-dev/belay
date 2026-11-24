import Belay

set_option doc.verso true

/-! Old step contracts for comparing single-table scans and derived-column migration outputs. -/

namespace Belay.Sqlite.Model
open Resolved

theorem runScriptStep_simpleTable_output_agree (context : ResolveContext) (clock : Option Clock)
    (before after : Nat) (connection expanded : Connection) (beforeStatement afterStatement : Syntax.Statement)
    (parameters : List Value) (beforePosition afterPosition : Nat) (table extended : Table)
    (beforeFilter afterFilter : Option Expr) (columns : List Resolved.Output)
    (beforeNames afterNames : List String) (width : Nat) (extra : List Value → List Value)
    {beforeState afterState : ResolveState}
    (resolvedBefore : resolveStatement context connection.resolveState beforeStatement =
      .ok (.query (Query.simple [QuerySource.first beforePosition] beforeFilter columns beforeNames) [], beforeState))
    (resolvedAfter : resolveStatement context expanded.resolveState afterStatement =
      .ok (.query (Query.simple [QuerySource.first afterPosition] afterFilter columns afterNames) [], afterState))
    (presentBefore : connection.state.database.table beforePosition = some table)
    (presentAfter : expanded.state.database.table afterPosition = some extended)
    (calmBefore : (Resolved.Statement.query
      (Query.simple [QuerySource.first beforePosition] beforeFilter columns beforeNames) []).Calm)
    (calmAfter : (Resolved.Statement.query
      (Query.simple [QuerySource.first afterPosition] afterFilter columns afterNames) []).Calm)
    (scans : sourceRows extended = (sourceRows table).map fun row => row ++ extra row)
    (wide : ∀ row ∈ sourceRows table, width ≤ row.length)
    (columnsBelow : ∀ column ∈ columns, column.readsBelow width = true)
    (agree : ∀ row ∈ sourceRows table,
      (afterFilter.all fun condition => truthy (condition.eval (EvalContext.bound parameters) (row ++ extra row))) =
        (beforeFilter.all fun condition => truthy (condition.eval (EvalContext.bound parameters) row))) :
    (runScriptStep context clock before connection beforeStatement parameters).output =
      (runScriptStep context clock after expanded afterStatement parameters).output := by
  rw [runScriptStep_output_of_resolved resolvedBefore, runScriptStep_output_of_resolved resolvedAfter]
  exact resolvedStepOutput_simpleTable_agree clock before after connection expanded parameters beforePosition
    afterPosition table extended beforeFilter afterFilter columns beforeNames afterNames width extra presentBefore
    presentAfter calmBefore calmAfter scans wide columnsBelow agree

theorem original_derivedColumn_lookup_outputs (context : ResolveContext) (clock : Option Clock) (before after : Nat)
    (connection migrated : Connection) (beforeStatement afterStatement : Syntax.Statement)
    (parameters : List Value) (position : Nat) (table : Table) (column : CatalogColumn) (derived : Resolved.Expr)
    (triggers : List (Identifier × CatalogTrigger)) (beforeFilter afterFilter : Option Expr)
    (columns : List Resolved.Output) (beforeNames afterNames : List String) {beforeState afterState : ResolveState}
    (present : connection.state.database.table position = some table)
    (aligned : position < connection.state.database.rows.length)
    (reached : migrated.state.database =
      connection.state.database.addDerivedColumn position table column derived triggers)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (below : derived.readsBelow table.shape.columns.length = true)
    (keysInside : ∀ key ∈ table.shape.primaryKey, key < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) (newPlain : column.generated = none)
    (resolvedBefore : resolveStatement context connection.resolveState beforeStatement =
      .ok (.query (Query.simple [QuerySource.first position] beforeFilter columns beforeNames) [], beforeState))
    (resolvedAfter : resolveStatement context migrated.resolveState afterStatement =
      .ok (.query (Query.simple [QuerySource.first position] afterFilter columns afterNames) [], afterState))
    (calmBefore : (Resolved.Statement.query
      (Query.simple [QuerySource.first position] beforeFilter columns beforeNames) []).Calm)
    (calmAfter : (Resolved.Statement.query
      (Query.simple [QuerySource.first position] afterFilter columns afterNames) []).Calm)
    (columnsBelow : ∀ output ∈ columns, output.readsBelow table.shape.columns.length = true)
    (agree : ∀ cells ∈ sourceRows table,
      (afterFilter.all fun condition => truthy (condition.eval (EvalContext.bound parameters)
        (cells ++ [Value.store column.affinity (derived.eval (EvalContext.plain 0) cells)]))) =
        (beforeFilter.all fun condition => truthy (condition.eval (EvalContext.bound parameters) cells))) :
    (runScriptStep context clock before connection beforeStatement parameters).output =
      (runScriptStep context clock after migrated afterStatement parameters).output := by
  rw [runScriptStep_output_of_resolved resolvedBefore, runScriptStep_output_of_resolved resolvedAfter]
  exact derivedColumn_lookup_outputs clock before after connection migrated parameters position table column derived triggers
    beforeFilter afterFilter columns beforeNames afterNames present aligned reached wide aliased below keysInside plain newPlain
    calmBefore calmAfter columnsBelow agree

theorem original_derivedColumn_preserved_outputs (context : ResolveContext) (clock : Option Clock) (before after : Nat)
    (connection migrated : Connection) (statement : Syntax.Statement) (parameters : List Value) (position : Nat)
    (table : Table) (column : CatalogColumn) (derived : Resolved.Expr) (triggers : List (Identifier × CatalogTrigger))
    (filter : Option Expr) (columns : List Resolved.Output) (names other : List String)
    {beforeState afterState : ResolveState}
    (present : connection.state.database.table position = some table)
    (aligned : position < connection.state.database.rows.length)
    (reached : migrated.state.database =
      connection.state.database.addDerivedColumn position table column derived triggers)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (below : derived.readsBelow table.shape.columns.length = true)
    (keysInside : ∀ key ∈ table.shape.primaryKey, key < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) (newPlain : column.generated = none)
    (resolvedBefore : resolveStatement context connection.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first position] filter columns names) [], beforeState))
    (resolvedAfter : resolveStatement context migrated.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first position] filter columns other) [], afterState))
    (calm : (Resolved.Statement.query (Query.simple [QuerySource.first position] filter columns names) []).Calm)
    (filterBelow : ∀ condition ∈ filter, condition.readsBelow table.shape.columns.length = true)
    (columnsBelow : ∀ output ∈ columns, output.readsBelow table.shape.columns.length = true) :
    (runScriptStep context clock before connection statement parameters).output =
      (runScriptStep context clock after migrated statement parameters).output := by
  rw [runScriptStep_output_of_resolved resolvedBefore, runScriptStep_output_of_resolved resolvedAfter]
  exact derivedColumn_preserved_outputs clock before after connection migrated parameters position table column derived triggers
    filter columns names other present aligned reached wide aliased below keysInside plain newPlain
    calm filterBelow columnsBelow

#print axioms runScriptStep_simpleTable_output_agree
#print axioms original_derivedColumn_lookup_outputs
#print axioms original_derivedColumn_preserved_outputs

end Belay.Sqlite.Model
