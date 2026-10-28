import Belay.Sqlite.ColumnQuery

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

-- Original Holds.iff_selectOne_column.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {subFilter : Option Syntax.Expr} {mainFilter : Syntax.Expr} {parameters : List Value}
    {rest : List (Syntax.Statement × List Value)} {position : Nat} {table : CatalogTable}
    {subCondition : Option Resolved.Expr} {mainCondition : Resolved.Expr} {value : Syntax.Expr}
    {expression : Resolved.Expr} {affinity : Option Affinity} {text : String}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none none
      [Syntax.Subquery.mk [.expression value none text] (some reference) [] subFilter [] [] none none none none
        false none none] none false none, parameters) :: rest)
    (notCall : value.isCall = false) (noAggregate : value.aggregateCalls.isEmpty = true)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (operand : resolveOperand runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      { current := some 0 } false value = .ok (expression, affinity))
    (valuePlain : expression.any Resolved.Expr.isFallibleCall = false)
    (subResolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (mainResolves : ∀ lowest : Option Nat,
      FilterResolves runContext.profile.dqsDml [] [] (some mainFilter) (some mainCondition)
        { later := [scalarShape affinity value.explicitCollation (value.columnCollation
          (tableScope db.raw.catalog reference position table)) lowest
          (value.originType (tableScope db.raw.catalog reference position table) { current := some 0 })] })
    (noScalar : mainCondition.any (· matches .subquery _) = false)
    (mainCalm : mainCondition.Calm) (subCalm : ∀ expression ∈ subCondition.toList, expression.Calm)
    (valueCalm : expression.Calm) :
    Holds script db isQuery ↔
      Resolved.truthy (mainCondition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.certain (Resolved.scalarRows (Resolved.EvalContext.bound parameters) subCondition expression
          { shape := table, rows := db.raw.rows.getD position [] })]) []) = true := by
  unfold Holds
  rw [Script.outputOn_column head notCall noAggregate namedSource current arguments found operand valuePlain subResolves mainResolves noScalar mainCalm subCalm valueCalm]
  simp [Output.hasRows, apply_ite]

-- Original Empty.iff_selectOne_column.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {subFilter : Option Syntax.Expr} {mainFilter : Syntax.Expr} {parameters : List Value}
    {rest : List (Syntax.Statement × List Value)} {position : Nat} {table : CatalogTable}
    {subCondition : Option Resolved.Expr} {mainCondition : Resolved.Expr} {value : Syntax.Expr}
    {expression : Resolved.Expr} {affinity : Option Affinity} {text : String}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none none
      [Syntax.Subquery.mk [.expression value none text] (some reference) [] subFilter [] [] none none none none
        false none none] none false none, parameters) :: rest)
    (notCall : value.isCall = false) (noAggregate : value.aggregateCalls.isEmpty = true)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (operand : resolveOperand runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      { current := some 0 } false value = .ok (expression, affinity))
    (valuePlain : expression.any Resolved.Expr.isFallibleCall = false)
    (subResolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (mainResolves : ∀ lowest : Option Nat,
      FilterResolves runContext.profile.dqsDml [] [] (some mainFilter) (some mainCondition)
        { later := [scalarShape affinity value.explicitCollation (value.columnCollation
          (tableScope db.raw.catalog reference position table)) lowest
          (value.originType (tableScope db.raw.catalog reference position table) { current := some 0 })] })
    (noScalar : mainCondition.any (· matches .subquery _) = false)
    (mainCalm : mainCondition.Calm) (subCalm : ∀ expression ∈ subCondition.toList, expression.Calm)
    (valueCalm : expression.Calm) :
    Empty script db isQuery ↔
      Resolved.truthy (mainCondition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.certain (Resolved.scalarRows (Resolved.EvalContext.bound parameters) subCondition expression
          { shape := table, rows := db.raw.rows.getD position [] })]) []) = false := by
  unfold Empty
  rw [Script.outputOn_column head notCall noAggregate namedSource current arguments found operand valuePlain subResolves mainResolves noScalar mainCalm subCalm valueCalm]
  simp [Output.hasNoRows, apply_ite]

-- Original Fails.not_selectOne_column.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {subFilter : Option Syntax.Expr} {mainFilter : Syntax.Expr} {parameters : List Value}
    {rest : List (Syntax.Statement × List Value)} {position : Nat} {table : CatalogTable}
    {subCondition : Option Resolved.Expr} {mainCondition : Resolved.Expr} {value : Syntax.Expr}
    {expression : Resolved.Expr} {affinity : Option Affinity} {text : String}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none none
      [Syntax.Subquery.mk [.expression value none text] (some reference) [] subFilter [] [] none none none none
        false none none] none false none, parameters) :: rest)
    (notCall : value.isCall = false) (noAggregate : value.aggregateCalls.isEmpty = true)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (operand : resolveOperand runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      { current := some 0 } false value = .ok (expression, affinity))
    (valuePlain : expression.any Resolved.Expr.isFallibleCall = false)
    (subResolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (mainResolves : ∀ lowest : Option Nat,
      FilterResolves runContext.profile.dqsDml [] [] (some mainFilter) (some mainCondition)
        { later := [scalarShape affinity value.explicitCollation (value.columnCollation
          (tableScope db.raw.catalog reference position table)) lowest
          (value.originType (tableScope db.raw.catalog reference position table) { current := some 0 })] })
    (noScalar : mainCondition.any (· matches .subquery _) = false)
    (mainCalm : mainCondition.Calm) (subCalm : ∀ expression ∈ subCondition.toList, expression.Calm)
    (valueCalm : expression.Calm) :
    ¬ Fails script db isQuery := by
  unfold Fails
  rw [Script.outputOn_column head notCall noAggregate namedSource current arguments found operand valuePlain subResolves mainResolves noScalar mainCalm subCalm valueCalm]
  simp [Output.isError, apply_ite]

end Belay.Sqlite
