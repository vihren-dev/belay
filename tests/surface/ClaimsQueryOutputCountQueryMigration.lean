import Belay.Sqlite.CountQuery

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

-- Original Holds.iff_selectOne_count.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {subFilter : Option Syntax.Expr} {mainFilter : Syntax.Expr} {parameters : List Value}
    {rest : List (Syntax.Statement × List Value)} {position : Nat} {table : CatalogTable}
    {subCondition : Option Resolved.Expr} {mainCondition : Resolved.Expr} {name : String} {text : String}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none none
      [Syntax.Subquery.mk [.expression (.callStar name) none text] (some reference) [] subFilter [] [] none none none none
        false none none] none false none, parameters) :: rest)
    (count : normalizeIdentifier name = "count")
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (subResolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (mainResolves : ∀ lowest : Option Nat,
      FilterResolves runContext.profile.dqsDml [] [] (some mainFilter) (some mainCondition) { later := [countShape lowest] })
    (mainCalm : mainCondition.Calm) (subCalm : ∀ expression ∈ subCondition.toList, expression.Calm) :
    Holds script db isQuery ↔
      Resolved.truthy (mainCondition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.count (Resolved.countMatching (Resolved.EvalContext.bound parameters) subCondition
          { shape := table, rows := db.raw.rows.getD position [] })]) []) = true := by
  unfold Holds
  rw [Script.outputOn_count head count namedSource current arguments found subResolves mainResolves mainCalm subCalm]
  simp [Output.hasRows, apply_ite]

-- Original Empty.iff_selectOne_count.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {subFilter : Option Syntax.Expr} {mainFilter : Syntax.Expr} {parameters : List Value}
    {rest : List (Syntax.Statement × List Value)} {position : Nat} {table : CatalogTable}
    {subCondition : Option Resolved.Expr} {mainCondition : Resolved.Expr} {name : String} {text : String}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none none
      [Syntax.Subquery.mk [.expression (.callStar name) none text] (some reference) [] subFilter [] [] none none none none
        false none none] none false none, parameters) :: rest)
    (count : normalizeIdentifier name = "count")
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (subResolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (mainResolves : ∀ lowest : Option Nat,
      FilterResolves runContext.profile.dqsDml [] [] (some mainFilter) (some mainCondition) { later := [countShape lowest] })
    (mainCalm : mainCondition.Calm) (subCalm : ∀ expression ∈ subCondition.toList, expression.Calm) :
    Empty script db isQuery ↔
      Resolved.truthy (mainCondition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.count (Resolved.countMatching (Resolved.EvalContext.bound parameters) subCondition
          { shape := table, rows := db.raw.rows.getD position [] })]) []) = false := by
  unfold Empty
  rw [Script.outputOn_count head count namedSource current arguments found subResolves mainResolves mainCalm subCalm]
  simp [Output.hasNoRows, apply_ite]

-- Original Fails.not_selectOne_count.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {subFilter : Option Syntax.Expr} {mainFilter : Syntax.Expr} {parameters : List Value}
    {rest : List (Syntax.Statement × List Value)} {position : Nat} {table : CatalogTable}
    {subCondition : Option Resolved.Expr} {mainCondition : Resolved.Expr} {name : String} {text : String}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none none
      [Syntax.Subquery.mk [.expression (.callStar name) none text] (some reference) [] subFilter [] [] none none none none
        false none none] none false none, parameters) :: rest)
    (count : normalizeIdentifier name = "count")
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (subResolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (mainResolves : ∀ lowest : Option Nat,
      FilterResolves runContext.profile.dqsDml [] [] (some mainFilter) (some mainCondition) { later := [countShape lowest] })
    (mainCalm : mainCondition.Calm) (subCalm : ∀ expression ∈ subCondition.toList, expression.Calm) :
    ¬ Fails script db isQuery := by
  unfold Fails
  rw [Script.outputOn_count head count namedSource current arguments found subResolves mainResolves mainCalm subCalm]
  simp [Output.isError, apply_ite]

end Belay.Sqlite
