import Belay.Sqlite.QueryBridge
import Belay.Sqlite.Model

set_option doc.verso true

/-! The query form {lit}`SELECT 1 WHERE c(SELECT count(*) FROM t WHERE p)` over every database (ADR 0017, S4):
a condition on the number of rows of {lit}`t` for which {lit}`p` is true, such as a bound
{lit}`(SELECT count(*) FROM t) < 100`. When the catalog of the database has the table and {lit}`p` resolves in the
scope of the table, the claims {lit}`Holds` and {lit}`Empty` of the query are statements about the condition
{lit}`c` with the number of rows as the value of the subquery, when the expressions of {lit}`c` and {lit}`p` are calm
(no fallible call, no clock read and no counter read) and {lit}`c` resolves for every shape of a count query. Then
{lit}`Fails` does not hold. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

/-- For every script whose first statement is {lit}`SELECT 1 WHERE c` with the subquery
{lit}`SELECT count(*) FROM t WHERE p`, where the catalog of the database has the table {lit}`t` at a position, {lit}`p`
resolves in the scope of the table, and {lit}`c` resolves, for every shape of a count query, to a condition
without a fallible call, the output of the script is the output of the step of the simple query without source
whose condition is the resolved {lit}`c`, with the count query of that table as its one subquery. The source reference has no indexed query.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch:
{name}`Script.outputOn_query` with the resolution of {name}`resolveStatement_selectOne_count`. -/
theorem Script.outputOn_selectOne_count
    {script : Script} {db : Database} {reference : Syntax.TableReference}
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
    (plain : mainCondition.any Resolved.Expr.isFallibleCall = false) :
    script.outputOn db = some (resolvedStepOutput none 0 db.raw.connection parameters
      (.query (Resolved.Query.selectOneWhere mainCondition)
        [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition text])) :=
  Script.outputOn_query script db _ parameters rest _ _ _ head
    (resolveStatement_selectOne_count runContext db.raw.connection.resolveState reference subFilter mainFilter position table
      subCondition mainCondition name text count namedSource current arguments found subResolves mainResolves plain)

/-- For every script with the resolution premises of {name}`Script.outputOn_selectOne_count`,
when the resolved expressions satisfy the stated calmness premises, its complete first output is
one row containing integer one when its condition on the certain count is true, and no rows
otherwise. The count includes exactly the source rows whose subquery condition is true.
Proof sketch: resolve once, then substitute {name}`resolvedStepOutput_count`. -/
theorem Script.outputOn_count
    {script : Script} {db : Database} {reference : Syntax.TableReference}
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
    script.outputOn db = some (.rows (if Resolved.truthy (mainCondition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.count (Resolved.countMatching (Resolved.EvalContext.bound parameters) subCondition { shape := table, rows := db.raw.rows.getD position [] })]) [])
        then [[.integer 1]] else [])) := by
  rw [Script.outputOn_selectOne_count head count namedSource current arguments found subResolves mainResolves mainCalm.1]
  exact congrArg some (resolvedStepOutput_count 0 db.raw.connection parameters mainCondition position
    { shape := table, rows := db.raw.rows.getD position [] } subCondition text (Database.table_of_findTable db.raw _ position table found)
    (Resolved.Statement.Calm.selectOne_count position _ subCondition text mainCalm subCalm))

end Belay.Sqlite
