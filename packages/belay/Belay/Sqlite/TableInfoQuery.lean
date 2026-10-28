import Belay.Sqlite.QueryBridge
import Belay.Sqlite.Model

set_option doc.verso true

/-! The query form {lit}`SELECT 1 FROM pragma_table_info('t') WHERE p` over every database (ADR 0017, S4): a statement of
the schema, such as "the table {lit}`t` has a column {lit}`c`". When the catalog of the database has no table or view with the name of
the function, the table lookup is by the name of the argument ({lit}`Catalog.tableInfoRows`), and {lit}`p` resolves in the
scope of the pragma, the claims {lit}`Holds` and {lit}`Empty` of the query are statements about the rows of the pragma and
the resolved condition, when the expressions of {lit}`p` are calm. Then {lit}`Fails` does not hold. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

/-- For every script whose first statement is {lit}`SELECT 1 FROM pragma_table_info('t') WHERE p` (or without
{lit}`WHERE`), where the catalog of the database has no table or view with the name of the function, gives rows for the table
{lit}`t` ({name}`Catalog.tableInfoRows`), and {lit}`p` resolves in the scope of the pragma ({name}`tableInfoScope`), the output
of the script is the output of the step of the simple query of the pragma source with those rows. The source reference has no indexed query.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch:
{name}`Script.outputOn_query` with the resolution of {name}`resolveStatement_select_one_tableInfo`. -/
theorem Script.outputOn_selectOne_tableInfo
    {script : Script} {db : Database} {reference : Syntax.TableReference}
    {filter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {argument : List UInt8} {rows : List (List Value)} {condition : Option Resolved.Expr}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] (some reference) [] filter [] [] none none []
      none false none, parameters) :: rest)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = some [.string argument])
    (isFunction : reference.table.isKeyword (bytes! "pragma_table_info") = true)
    (notTable : db.raw.catalog.findTable reference.table = none)
    (notView : db.raw.catalog.findView reference.table = none)
    (info : db.raw.catalog.tableInfoRows ⟨argument⟩ = some rows)
    (resolves : FilterResolves runContext.profile.dqsDml (tableInfoScope reference argument rows) [] filter condition) :
    script.outputOn db = some (resolvedStepOutput none 0 db.raw.connection parameters
      (.query (Resolved.Query.simple [Resolved.QuerySource.pragma (pragmaSource reference argument tableInfoNames rows).1] condition
        [.scalar (.literal (.integer 1))] ["1"]) [])) :=
  Script.outputOn_query script db _ parameters rest _ [] _ head
    (resolveStatement_select_one_tableInfo runContext db.raw.connection.resolveState reference argument rows filter condition
      namedSource current arguments isFunction notTable notView info resolves)

/-- For every script with the resolution premises of {name}`Script.outputOn_selectOne_tableInfo`,
when the resolved expressions satisfy the stated calmness premises, its complete first output is
one row containing integer one for each metadata row that passes its condition, in normal
form. The condition sees both appended hidden cells: the argument text and NULL.
Proof sketch: resolve once, then substitute {name}`resolvedStepOutput_simplePragma`. -/
theorem Script.outputOn_tableInfo
    {script : Script} {db : Database} {reference : Syntax.TableReference}
    {filter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {argument : List UInt8} {rows : List (List Value)} {condition : Option Resolved.Expr}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] (some reference) [] filter [] [] none none []
      none false none, parameters) :: rest)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = some [.string argument])
    (isFunction : reference.table.isKeyword (bytes! "pragma_table_info") = true)
    (notTable : db.raw.catalog.findTable reference.table = none)
    (notView : db.raw.catalog.findView reference.table = none)
    (info : db.raw.catalog.tableInfoRows ⟨argument⟩ = some rows)
    (resolves : FilterResolves runContext.profile.dqsDml (tableInfoScope reference argument rows) [] filter condition)
    (calm : ∀ expression ∈ condition.toList, expression.Calm) :
    script.outputOn db = some (.rows (Resolved.normalForm
      (((rows.map (· ++ [Value.text argument, Value.null])).filter fun row => condition.all
        (fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row))).map
          fun _ => [Value.integer 1]))) := by
  rw [Script.outputOn_selectOne_tableInfo head namedSource current arguments isFunction notTable notView info resolves]
  exact congrArg some (resolvedStepOutput_simplePragma 0 db.raw.connection parameters _ _ condition _ _
    (Resolved.Statement.Calm.selectOne_pragma _ condition calm))

end Belay.Sqlite
