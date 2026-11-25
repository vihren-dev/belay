import Belay

set_option doc.verso true

/-! A query send checks the continuation for the raw observation and every concrete choice. -/

namespace QuerySendClaims
open Belay.Sqlite Model

/-- On any valid connection on which the sent query is modeled, the next program step sees
the same connection and the returned singleton output in the trace. This includes a SQLite
error, raw choices and their selected rows. Proof sketch: the query rule has one execution
and the continuation runs for each selected output. -/
theorem selected_output_in_trace (ctx : ExecutionContext) (stmt : Syntax.Statement)
    (parameters : List Value) (query : Resolved.Query) (subqueries : List Resolved.Query) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.query query subqueries, after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (do let outputs ← send ⟨[(stmt, parameters)]⟩
        pure outputs).check (fun outputs final => final.connection = ctx.connection ∧
          final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨rfl, rfl⟩ | trivial

#print axioms selected_output_in_trace

end QuerySendClaims
