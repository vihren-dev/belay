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

/-- For a script beginning with a successfully resolved statement of any kind, its observed
output is the resolved statement's output on the observation connection, at its clock and
index. Proof sketch: take the first step output and substitute the resolution. -/
theorem Script.outputOn_resolved (script : Script) (db : Database) (statement : Syntax.Statement)
    (parameters : List Value) (rest : List (Syntax.Statement × List Value))
    (kind : Resolved.Statement) (after : ResolveState)
    (head : script.statements = (statement, parameters) :: rest)
    (resolved : resolveStatement runContext db.raw.connection.resolveState statement =
      .ok (kind, after)) :
    script.outputOn db =
      some (resolvedStepOutput none 0 db.raw.connection parameters kind) := by
  rw [Script.outputOn_eq_step script db statement parameters rest head, resolved]

end Belay.Sqlite
