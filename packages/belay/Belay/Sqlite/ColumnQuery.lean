import Belay.Sqlite.QueryBridge
import Belay.Sqlite.Model

set_option doc.verso true

/-! The query form {lit}`SELECT 1 WHERE c(SELECT e FROM t WHERE p)` over every database (ADR 0017, S4): a condition
{lit}`c` on a subquery with one column, such as {lit}`$x IN (SELECT id FROM t WHERE p)`. When the catalog of the database
has the table, {lit}`e` is no function call and resolves in the scope of the table, {lit}`p` resolves in the scope of
the table, and {lit}`c` resolves for every shape of a one-column subquery, the claims {lit}`Holds` and {lit}`Empty` of
the query are statements about the condition {lit}`c` with the values of {lit}`e` for the kept rows as the rows of the
subquery, when the expressions of {lit}`c`, {lit}`p` and {lit}`e` are calm and {lit}`c` reads no scalar subquery. Then
{lit}`Fails` does not hold. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

/-- For every script whose first statement is {lit}`SELECT 1 WHERE c` with the subquery {lit}`SELECT e FROM t WHERE p`,
where the catalog of the database has the table {lit}`t` at a position, {lit}`e` is no function call, has no aggregate call
and resolves in the scope of the table to an expression without a fallible call, {lit}`p` resolves in the scope of the table,
and {lit}`c` resolves, for every lowest position of a subquery with one column and
the declared-type origin of {lit}`e` ({name}`scalarShape`), to a condition without a
fallible call, the output of the script is the output of the step of the simple query without source whose condition is the
resolved {lit}`c`, with the simple query of that table with the resolved {lit}`p` and {lit}`e` as its one subquery. The source reference has no indexed query.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch:
{name}`Script.outputOn_query` with the resolution of {name}`resolveStatement_selectOne_scalar`. -/
theorem Script.outputOn_selectOne_column
    {script : Script} {db : Database} {reference : Syntax.TableReference}
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
    (plain : mainCondition.any Resolved.Expr.isFallibleCall = false) :
    script.outputOn db = some (resolvedStepOutput none 0 db.raw.connection parameters
      (.query (Resolved.Query.selectOneWhere mainCondition)
        [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition [.scalar expression]
          [(definedName (tableScope db.raw.catalog reference position table) value).getD text]])) :=
  Script.outputOn_query script db _ parameters rest _ _ _ head
    (resolveStatement_selectOne_scalar runContext db.raw.connection.resolveState reference value text subFilter mainFilter
      position table subCondition mainCondition expression affinity notCall noAggregate namedSource current arguments found operand valuePlain
      subResolves mainResolves plain)

/-- For every script with the resolution premises of {name}`Script.outputOn_selectOne_column`,
when the resolved expressions satisfy the stated calmness premises, its complete first output is
one row containing integer one when its condition on the filtered column values is true,
and no rows otherwise.
The outer condition excludes scalar subqueries but permits membership. Proof sketch: resolve once, then substitute {name}`resolvedStepOutput_scalar`. -/
theorem Script.outputOn_column
    {script : Script} {db : Database} {reference : Syntax.TableReference}
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
    script.outputOn db = some (.rows (if Resolved.truthy (mainCondition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.certain
          (Resolved.scalarRows (Resolved.EvalContext.bound parameters) subCondition expression { shape := table, rows := db.raw.rows.getD position [] })]) [])
        then [[.integer 1]] else [])) := by
  rw [Script.outputOn_selectOne_column head notCall noAggregate namedSource current arguments found operand valuePlain subResolves mainResolves mainCalm.1]
  exact congrArg some (resolvedStepOutput_scalar 0 db.raw.connection parameters mainCondition position
    { shape := table, rows := db.raw.rows.getD position [] } subCondition expression _ (Database.table_of_findTable db.raw _ position table found) noScalar
    (Resolved.Statement.Calm.selectOne_scalar position _ subCondition expression _ mainCalm subCalm valueCalm))

end Belay.Sqlite
