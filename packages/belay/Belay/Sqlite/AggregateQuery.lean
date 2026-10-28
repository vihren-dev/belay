import Belay.Sqlite.QueryBridge
import Belay.Sqlite.Model

set_option doc.verso true

/-! The query form {lit}`SELECT agg(x) FROM t WHERE p` over every database (ADR 0017, S4), where {lit}`agg` is an
aggregate of one operand, such as {lit}`SELECT sum(c) FROM t`: the whole table is one group, so the query has one row,
also for a table without a row, unless the aggregate fails. The only aggregate that fails is {lit}`sum`, with
{lit}`integer overflow`. When the catalog of the database has the table, and the operand and {lit}`p` resolve in the
scope of the table to expressions that are calm (no fallible call, no clock read and no counter read), the claims
{lit}`Holds` and {lit}`Fails` of the query are statements about the aggregate over the rows of the table that
{lit}`p` keeps, and {lit}`Empty` does not hold. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

/-- For every script whose first statement is {lit}`SELECT agg(x) FROM t WHERE p` (or without {lit}`WHERE`), where the
catalog of the database has the table {lit}`t` at a position, the name {lit}`agg` names an aggregate of one operand that
does not write JSON ({name}`aggregateNamed`), and the operand and {lit}`p` resolve in the scope of the table, the output
of the script is the output of the step of the whole-table aggregate query of that table
({name}`Resolved.Query.aggregateOf`). The source reference has no indexed query.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch: {name}`Script.outputOn_query` with the resolution of
{name}`resolveStatement_select_aggregate`. -/
theorem Script.outputOn_selectAggregate
    {script : Script} {db : Database} {reference : Syntax.TableReference} {filter : Option Syntax.Expr}
    {parameters : List Value} {rest : List (Syntax.Statement × List Value)} {position : Nat} {table : CatalogTable}
    {condition : Option Resolved.Expr} {name : String} {operand : Syntax.Expr} {alias : Option Identifier}
    {text : String} {build : Resolved.Expr → Resolved.Aggregate} {resolved : Resolved.Expr}
    {affinity : Option Affinity} {aggregate : Resolved.Aggregate}
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
      (build resolved).withCollation (operand.collationIn (tableScope db.raw.catalog reference position table))) :
    script.outputOn db = some (resolvedStepOutput none 0 db.raw.connection parameters
      (.query (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate
        ((alias.map (·.text)).getD text)) [])) := by
  subst aggregateIs
  exact Script.outputOn_query script db _ parameters rest _ [] _ head
    (resolveStatement_select_aggregate runContext db.raw.connection.resolveState reference filter name operand alias text
      build named position table resolved affinity condition namedSource current arguments found operandOk noJson resolves)

/-- For every script with the resolution premises of {name}`Script.outputOn_selectAggregate`,
when the resolved expressions satisfy the stated calmness premises, its complete first output is
an integer-overflow error when the aggregate fails on the rows kept by its filter; otherwise
it gives every aggregate result, including the aggregate row on empty input.
Proof sketch: resolve once, then substitute {name}`resolvedStepOutput_aggregateTable`. -/
theorem Script.outputOn_aggregate
    {script : Script} {db : Database} {reference : Syntax.TableReference}
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
    script.outputOn db = some (if aggregate.fails (Resolved.EvalContext.bound parameters) ((Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }).filter fun row =>
          condition.all fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row))
        then .error ExecutionError.integerOverflow.primaryCode
        else Output.ofResults ((Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate ((alias.map (·.text)).getD text)).possibleResults
           (Resolved.EvalContext.bound parameters) (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }))) := by
  rw [Script.outputOn_selectAggregate head named namedSource current arguments found operandOk noJson resolves aggregateIs]
  exact congrArg some (resolvedStepOutput_aggregateTable 0 position db.raw.connection parameters
    { shape := table, rows := db.raw.rows.getD position [] } condition aggregate _
    (Database.table_of_findTable db.raw _ position table found)
    (Resolved.Statement.Calm.aggregateOf_first position _ aggregate _ conditionCalm operandsCalm))

end Belay.Sqlite
