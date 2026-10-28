import Belay.Sqlite.AggregateQuery

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

-- Original Holds.iff_selectAggregate.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {filter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {position : Nat} {table : CatalogTable} {condition : Option Resolved.Expr} {name : String}
    {operand : Syntax.Expr} {alias : Option Identifier} {text : String} {build : Resolved.Expr → Resolved.Aggregate}
    {resolved : Resolved.Expr} {affinity : Option Affinity} {aggregate : Resolved.Aggregate}
    (head : script.statements = (.select [.expression (.call name [operand]) alias text] (some reference) [] filter [] []
      none none [] none false none, parameters) :: rest)
    (named : aggregateNamed name = some build) (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : db.raw.catalog.findTable reference.table = some (position, table))
    (operandOk : resolveOperand runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      { current := none, later := [] } true operand = .ok (resolved, affinity))
    (noJson : (build resolved).writesJson = false)
    (resolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      ((resultAliases (tableScope db.raw.catalog reference position table)
        [.expression (.call name [operand]) alias text]).filterMap id) filter condition { current := none, later := [] })
    (aggregateIs : aggregate =
      (build resolved).withCollation (operand.collationIn (tableScope db.raw.catalog reference position table)))
    (conditionCalm : ∀ expression ∈ condition.toList, expression.Calm)
    (operandsCalm : ∀ expression ∈ (Resolved.Output.aggregate aggregate).operands, expression.Calm) :
    Holds script db isQuery ↔
      aggregate.fails (Resolved.EvalContext.bound parameters)
        ((Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }).filter fun row =>
          condition.all fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) =
        false := by
  unfold Holds
  rw [Script.outputOn_aggregate head named namedSource current arguments found operandOk noJson resolves aggregateIs conditionCalm operandsCalm]
  simp [Output.hasRows, apply_ite, Resolved.Query.aggregateOf_possibleResults, Resolved.Query.aggregateOf_filtered, Output.ofResults_singleton]

-- Original Empty.not_selectAggregate.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {filter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {position : Nat} {table : CatalogTable} {condition : Option Resolved.Expr} {name : String}
    {operand : Syntax.Expr} {alias : Option Identifier} {text : String} {build : Resolved.Expr → Resolved.Aggregate}
    {resolved : Resolved.Expr} {affinity : Option Affinity} {aggregate : Resolved.Aggregate}
    (head : script.statements = (.select [.expression (.call name [operand]) alias text] (some reference) [] filter [] []
      none none [] none false none, parameters) :: rest)
    (named : aggregateNamed name = some build) (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : db.raw.catalog.findTable reference.table = some (position, table))
    (operandOk : resolveOperand runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      { current := none, later := [] } true operand = .ok (resolved, affinity))
    (noJson : (build resolved).writesJson = false)
    (resolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      ((resultAliases (tableScope db.raw.catalog reference position table)
        [.expression (.call name [operand]) alias text]).filterMap id) filter condition { current := none, later := [] })
    (aggregateIs : aggregate =
      (build resolved).withCollation (operand.collationIn (tableScope db.raw.catalog reference position table)))
    (conditionCalm : ∀ expression ∈ condition.toList, expression.Calm)
    (operandsCalm : ∀ expression ∈ (Resolved.Output.aggregate aggregate).operands, expression.Calm) :
    ¬ Empty script db isQuery := by
  unfold Empty
  rw [Script.outputOn_aggregate head named namedSource current arguments found operandOk noJson resolves aggregateIs conditionCalm operandsCalm]
  simp [Output.hasNoRows, apply_ite, Resolved.Query.aggregateOf_possibleResults, Resolved.Query.aggregateOf_filtered, Output.ofResults_singleton]

-- Original Fails.iff_selectAggregate.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {filter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {position : Nat} {table : CatalogTable} {condition : Option Resolved.Expr} {name : String}
    {operand : Syntax.Expr} {alias : Option Identifier} {text : String} {build : Resolved.Expr → Resolved.Aggregate}
    {resolved : Resolved.Expr} {affinity : Option Affinity} {aggregate : Resolved.Aggregate}
    (head : script.statements = (.select [.expression (.call name [operand]) alias text] (some reference) [] filter [] []
      none none [] none false none, parameters) :: rest)
    (named : aggregateNamed name = some build) (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : db.raw.catalog.findTable reference.table = some (position, table))
    (operandOk : resolveOperand runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      { current := none, later := [] } true operand = .ok (resolved, affinity))
    (noJson : (build resolved).writesJson = false)
    (resolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      ((resultAliases (tableScope db.raw.catalog reference position table)
        [.expression (.call name [operand]) alias text]).filterMap id) filter condition { current := none, later := [] })
    (aggregateIs : aggregate =
      (build resolved).withCollation (operand.collationIn (tableScope db.raw.catalog reference position table)))
    (conditionCalm : ∀ expression ∈ condition.toList, expression.Calm)
    (operandsCalm : ∀ expression ∈ (Resolved.Output.aggregate aggregate).operands, expression.Calm) :
    Fails script db isQuery ↔
      aggregate.fails (Resolved.EvalContext.bound parameters)
        ((Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }).filter fun row =>
          condition.all fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) =
        true := by
  unfold Fails
  rw [Script.outputOn_aggregate head named namedSource current arguments found operandOk noJson resolves aggregateIs conditionCalm operandsCalm]
  simp [Output.isError, apply_ite, Resolved.Query.aggregateOf_possibleResults, Resolved.Query.aggregateOf_filtered, Output.ofResults_singleton]

end Belay.Sqlite
