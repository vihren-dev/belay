import QueryCount
import Belay.Sqlite.CountQuery

set_option doc.verso true

namespace ProofBoundaries
open Belay.Sqlite Belay.Sqlite.Model

/-- Under every original resolver, table, parameter and calmness premise of the surface
count-query contract, the script holds exactly when its condition is true with the number
of matching rows as its subquery value. An empty table contributes zero. Proof sketch:
resolve the script once, transport the row observer, and apply the new count semantics. -/
theorem surface_count_holds
    {script : Script} {db : Belay.Sqlite.Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {subFilter : Option Syntax.Expr} {mainFilter : Syntax.Expr} {parameters : List Value}
    {rest : List (Syntax.Statement × List Value)} {position : Nat} {table : CatalogTable}
    {subCondition : Option Resolved.Expr} {mainCondition : Resolved.Expr} {name : String} {text : String}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none none
      [Syntax.Subquery.mk [.expression (.callStar name) none text] (some reference) [] subFilter [] [] none none none none
        false none none] none false none, parameters) :: rest)
    (count : normalizeIdentifier name = "count")
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : db.raw.catalog.findTable reference.table = some (position, table))
    (subResolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (mainResolves : ∀ lowest : Option Nat,
      FilterResolves runContext.profile.dqsDml [] [] (some mainFilter) (some mainCondition) { later := [countShape lowest] })
    (mainCalm : mainCondition.Calm) (subCalm : ∀ expression ∈ subCondition.toList, expression.Calm) :
    Holds script db isQuery ↔
      Resolved.truthy (mainCondition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.count (Resolved.countMatching (Resolved.EvalContext.bound parameters) subCondition
          { shape := table, rows := db.raw.rows.getD position [] })]) []) = true := by
  have observed := Script.outputOn_selectOne_count head count namedSource current arguments found
    subResolves mainResolves mainCalm.1
  exact (observe_test_eq observed Output.hasRows).trans
    (count_hasRows 0 db.raw.connection parameters mainCondition position
      { shape := table, rows := db.raw.rows.getD position [] } subCondition text
      (Database.table_of_findTable db.raw _ position table found)
      (Resolved.Statement.Calm.selectOne_count position _ subCondition text mainCalm subCalm))

#print axioms surface_count_holds
end ProofBoundaries
