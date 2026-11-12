import Belay.Sqlite.Programs.Claims.QueryLaws

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every script that starts with a statement and every database, the output of the script
({name}`Script.outputOn`) is the output of the step of the statement on the connection to the
database ({name}`runScriptStep_output`): the reason of the restriction when resolution refuses it,
and otherwise {name}`resolvedStepOutput` of the resolved statement. Proof sketch: the first output of
a run is the output of its first step ({name}`runScriptFrom_head_cons`). -/
theorem Script.outputOn_eq_step (script : Script) (db : Database) (statement : Syntax.Statement)
    (parameters : List Value) (rest : List (Syntax.Statement × List Value))
    (head : script.statements = (statement, parameters) :: rest) :
    script.outputOn db =
      some (match resolveStatement runContext db.raw.connection.resolveState statement with
        | .error restriction => .unmodeled restriction.reason
        | .ok (resolved, _) => resolvedStepOutput none 0 db.raw.connection parameters resolved) := by
  unfold Script.outputOn Database.Raw.run Script.runOn
  rw [head, runScriptFrom_head_cons, runScriptStep_output]
  rfl

/-- For every script that starts with a statement that resolution turns into the query
{lit}`query` with the subqueries {lit}`subqueries`, the output of the script is the output of the step
of that query. Proof sketch: {name}`Script.outputOn_eq_step` with the resolved statement. -/
theorem Script.outputOn_query (script : Script) (db : Database) (statement : Syntax.Statement)
    (parameters : List Value) (rest : List (Syntax.Statement × List Value))
    (query : Resolved.Query) (subqueries : List Resolved.Query) (after : ResolveState)
    (head : script.statements = (statement, parameters) :: rest)
    (resolved : resolveStatement runContext db.raw.connection.resolveState statement =
      .ok (.query query subqueries, after)) :
    script.outputOn db =
      some (resolvedStepOutput none 0 db.raw.connection parameters (.query query subqueries)) := by
  rw [Script.outputOn_eq_step script db statement parameters rest head, resolved]

end Belay.Sqlite
