import ReplacedGeneralSend
import ReplacedPlainDrop
import ReplacedCatalogRewrite
import ReplacedCatalogContinuation

set_option doc.verso true

/-! The former schema statements of ADR 0033, derived with their original premises. -/

namespace Belay.Sqlite.ReplacedSchema
open Belay.Sqlite Model Model.ReplacedSchema

/-- The deleted law {lit}`Sql.check_send_dropPlain`. For every context, statement, values and post, with a valid connection in the context: the program that
sends the statement checks the post when these premises hold.
* {lit}`found`: the statement resolves from the connection to DROP TABLE of the objects at {lit}`positions`
  without rules, which is the resolution while foreign-key enforcement is off and no trigger fires.
* {lit}`success`: for every output that is not an error and does not end the run, and for the connection with the
  database without the objects ({name}`Model.Database.drop`): if that connection is valid, the post holds for
  the list of that one output and the context after it.
In plain words, a drop without rules never fails. Proof sketch: apply the common send bridge and the model witnesses for the cases. -/
theorem Sql.check_send_dropPlain {ctx : ExecutionContext} {statement : Syntax.Statement}
    {values : List Value} {positions : List Nat} {after : ResolveState}
    {post : List Output → ExecutionContext → Prop}
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState statement = .ok (.drop positions none, after))
    (success : ∀ (output : Output) (next : Connection), output.isError = false → output.endsRun = false →
      next = ctx.connection.withDatabase (ctx.connection.state.database.drop positions) →
      next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  obtain ⟨output, next, step⟩ := runScriptStep_drop_continues (parameters := values) (clock := ctx.clock)
    (index := ctx.index) found
  refine ReplacedGeneral.Sql.check_send_of_step (fun _ _ resolved => by
      obtain rfl := (Prod.mk.inj (Except.ok.inj (resolved.symm.trans found))).1
      rfl) ⟨output, next, [], step⟩
    (fun _ _ _ step => runScriptStep_ne_oneOf_of_not_query found (by intro _ _ same; cases same) step) ?_ valid
  intro output next step' hvalid
  obtain ⟨noError, -, nextEq⟩ := runScriptStep_drop_plain found step'
  exact success output next noError (runScriptStep_continued step').2 nextEq hvalid

/-- The deleted law {lit}`Sql.check_send_rewrite`. For every context, statement, values and post, with a valid connection in the context: the program that
sends the statement checks the post when these premises hold.
* {lit}`found`: the statement resolves from the connection to a rewrite of the catalog to {lit}`renamed`, as a
  rename does.
* {lit}`success`: for every output that is not an error and does not end the run, and for the connection with the
  database whose catalog is {lit}`renamed` and whose rows stay: if that connection is valid, the post holds for
  the list of that one output and the context after it.
In plain words, a resolved rename keeps the outline and succeeds. Proof sketch: apply the common send bridge and the model witnesses for the cases. -/
theorem Sql.check_send_rewrite {ctx : ExecutionContext} {statement : Syntax.Statement}
    {values : List Value} {renamed : Catalog} {after : ResolveState}
    {post : List Output → ExecutionContext → Prop}
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState statement = .ok (.rewrite renamed, after))
    (success : ∀ (output : Output) (next : Connection), output.isError = false → output.endsRun = false →
      next = ctx.connection.withDatabase { ctx.connection.state.database with catalog := renamed } →
      next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  obtain ⟨output, next, step, _⟩ := runScriptStep_rewrite_ok (parameters := values) (clock := ctx.clock)
    (index := ctx.index) found valid.1
  refine ReplacedGeneral.Sql.check_send_of_step (fun _ _ resolved => by
      obtain rfl := (Prod.mk.inj (Except.ok.inj (resolved.symm.trans found))).1
      rfl) ⟨output, next, [], step⟩
    (fun _ _ _ step => runScriptStep_ne_oneOf_of_not_query found (by intro _ _ same; cases same) step) ?_ valid
  intro output next step' hvalid
  obtain ⟨noError, -, -, nextEq⟩ := runScriptStep_rewrite found step'
  exact success output next noError (runScriptStep_continued step').2 nextEq hvalid

#print axioms Sql.check_send_dropPlain
#print axioms Sql.check_send_rewrite

end Belay.Sqlite.ReplacedSchema
