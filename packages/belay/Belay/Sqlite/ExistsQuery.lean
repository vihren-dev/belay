import Belay.Sqlite.QueryBridge
import Belay.Sqlite.Model

set_option doc.verso true

/-! The query form {lit}`SELECT 1 WHERE EXISTS (SELECT 1 FROM t WHERE p)` over every database (ADR 0017, S4):
"some row of {lit}`t` satisfies {lit}`p`". When the catalog of the database has the table and {lit}`p` resolves in the
scope of the table, the claims {lit}`Holds` and {lit}`Empty` of the query are statements about the rows of the
table and the resolved condition, and {lit}`Fails` does not hold. The form {lit}`NOT EXISTS` is in
{lit}`NotExistsQuery.lean`. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

/-- For every script whose first statement is {lit}`SELECT 1 WHERE EXISTS (SELECT 1 FROM t WHERE p)`, where the
catalog of the database has the table {lit}`t` at a position and {lit}`p` resolves in the scope of the table, the
output of the script is the output of the step of the simple query without source whose condition is
{lit}`EXISTS` of subquery 0, with the simple query of that table as its one subquery. The source reference has no indexed query.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch:
{name}`Script.outputOn_query` with the resolution of {name}`resolveStatement_selectOne_exists`. -/
theorem Script.outputOn_selectOne_exists
    {script : Script} {db : Database} {reference : Syntax.TableReference}
    {subFilter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {position : Nat} {table : CatalogTable} {subCondition : Option Resolved.Expr}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some (.exists 0)) [] [] none none
      [Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some reference) [] subFilter [] [] none none none none false none none]
      none false none, parameters) :: rest)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (resolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 }) :
    script.outputOn db = some (resolvedStepOutput none 0 db.raw.connection parameters
      (.query (Resolved.Query.selectOneWhere (.exists 0))
        [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition [.scalar (.literal (.integer 1))] ["1"]])) :=
  Script.outputOn_query script db _ parameters rest _ _ _ head
    (resolveStatement_selectOne_exists runContext db.raw.connection.resolveState reference subFilter position table
      subCondition namedSource current arguments found resolves)

/-- For every script with the resolution premises of {name}`Script.outputOn_selectOne_exists`,
when the resolved expressions satisfy the stated calmness premises, its complete first output is
one row containing integer one when a source row matches, and no rows otherwise.
Proof sketch: resolve once, then substitute {name}`resolvedStepOutput_exists`. -/
theorem Script.outputOn_exists
    {script : Script} {db : Database} {reference : Syntax.TableReference}
    {subFilter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {position : Nat} {table : CatalogTable} {subCondition : Option Resolved.Expr}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some (.exists 0)) [] [] none none
      [Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some reference) [] subFilter [] [] none none none none false none none]
      none false none, parameters) :: rest)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (resolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (calm : ∀ expression ∈ subCondition.toList, expression.Calm) :
    script.outputOn db = some (.rows (if (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }).any (fun row => subCondition.all
        (fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)))
        then [[.integer 1]] else [])) := by
  rw [Script.outputOn_selectOne_exists head namedSource current arguments found resolves]
  exact congrArg some (resolvedStepOutput_exists 0 position db.raw.connection parameters
    { shape := table, rows := db.raw.rows.getD position [] } subCondition _ _ (Database.table_of_findTable db.raw _ position table found)
    (Resolved.Statement.Calm.selectOne_subquery position _ subCondition (Resolved.Expr.calm_exists _) calm))

end Belay.Sqlite
