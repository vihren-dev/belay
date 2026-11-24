import ReplacedTransaction
import ReplacedControlFrame
import ReplacedSetting
import ReplacedControlContinuation

set_option doc.verso true

/-! Temporary witnesses for the control and pragma rules of ADR 0033. The exact rules
prove the original statements with their original premises. -/

namespace Belay.Sqlite
open Model

/-- The connection after BEGIN: when no transaction is open, the snapshot of the database opens one; when one is
open, the connection stays, because BEGIN fails. -/
def Model.Connection.afterBegin (connection : Connection) : Connection :=
  match connection.state.snapshot with
  | none => { connection with state := { connection.state with snapshot := some connection.state.database } }
  | some _ => connection

/-- The connection after COMMIT: the open transaction closes; when none is open, the connection stays, because
COMMIT fails. -/
def Model.Connection.afterCommit (connection : Connection) : Connection :=
  match connection.state.snapshot with
  | none => connection
  | some _ => { connection with state := { connection.state with snapshot := none } }

end Belay.Sqlite

namespace Belay.Sqlite.ReplacedControls
open Belay.Sqlite Model Model.ReplacedControls

/-- The deleted law {lit}`Sql.check_send_begin`. For every context, statement, values and post, with a valid connection in the context: the program that
sends the statement checks the post when these premises hold.
* {lit}`found`: the statement resolves from the connection to BEGIN.
* {lit}`success`: for every output that is an error exactly when a transaction is open, that does not end the
  run, and for the connection that {name}`Model.Connection.afterBegin` gives: if that connection is valid, the post
  holds for the list of that one output and the context after it.
In plain words, BEGIN opens a transaction when none is open, and fails without a change when one is open. Proof
sketch: {name}`Sql.check_send_of_step`, the continuation law {name}`Model.ReplacedControls.runScriptStep_begin_continues` and the step
laws {name}`Model.ReplacedControls.runScriptStep_begin_idle` and {name}`Model.ReplacedControls.runScriptStep_begin_active`. -/
theorem Sql.check_send_begin {ctx : ExecutionContext} {statement : Syntax.Statement}
    {values : List Value} {after : ResolveState} {post : List Output → ExecutionContext → Prop}
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState statement = .ok (.begin, after))
    (success : ∀ (output : Output) (next : Connection),
      output.isError = ctx.connection.state.snapshot.isSome → output.endsRun = false →
      next = ctx.connection.afterBegin →
      next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  obtain ⟨output, next, step⟩ := runScriptStep_begin_continues (parameters := values) (clock := ctx.clock)
    (index := ctx.index) found
  refine Sql.check_send_of_step (fun _ _ resolved => by
      obtain rfl := (Prod.mk.inj (Except.ok.inj (resolved.symm.trans found))).1
      rfl) ⟨output, next, [], step⟩
    (fun _ _ _ step => runScriptStep_ne_oneOf_of_not_query found (by intro _ _ same; cases same) step) ?_ valid
  intro output next step' hvalid
  have ends := (runScriptStep_continued step').2
  cases snapshot : ctx.connection.state.snapshot with
  | none =>
    obtain ⟨noError, -, nextEq⟩ := runScriptStep_begin_idle found snapshot step'
    exact success output next (by simp [noError, snapshot]) ends (by simp [Model.Connection.afterBegin, snapshot, nextEq])
      hvalid
  | some original =>
    obtain ⟨failed, -, nextEq⟩ := runScriptStep_begin_active found snapshot step'
    exact success output next (by simp [failed, snapshot]) ends (by simp [Model.Connection.afterBegin, snapshot, nextEq])
      hvalid

/-- The deleted law {lit}`Sql.check_send_commit`. For every context, statement, values and post, with a valid connection in the context: the program that
sends the statement checks the post when these premises hold.
* {lit}`found`: the statement resolves from the connection to COMMIT.
* {lit}`success`: for every output that is an error exactly when no transaction is open, that does not end the
  run, and for the connection that {name}`Model.Connection.afterCommit` gives: if that connection is valid, the
  post holds for the list of that one output and the context after it.
In plain words, COMMIT closes the open transaction, and fails without a change when none is open. Proof sketch: as
{name}`Sql.check_send_begin`, with {name}`Model.ReplacedControls.runScriptStep_commit_continues`, {name}`Model.ReplacedControls.runScriptStep_commit_active` and
{name}`Model.ReplacedControls.runScriptStep_commit_idle`. -/
theorem Sql.check_send_commit {ctx : ExecutionContext} {statement : Syntax.Statement}
    {values : List Value} {after : ResolveState} {post : List Output → ExecutionContext → Prop}
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState statement = .ok (.commit, after))
    (success : ∀ (output : Output) (next : Connection),
      output.isError = ctx.connection.state.snapshot.isNone → output.endsRun = false →
      next = ctx.connection.afterCommit →
      next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  obtain ⟨output, next, step⟩ := runScriptStep_commit_continues (parameters := values) (clock := ctx.clock)
    (index := ctx.index) found
  refine Sql.check_send_of_step (fun _ _ resolved => by
      obtain rfl := (Prod.mk.inj (Except.ok.inj (resolved.symm.trans found))).1
      rfl) ⟨output, next, [], step⟩
    (fun _ _ _ step => runScriptStep_ne_oneOf_of_not_query found (by intro _ _ same; cases same) step) ?_ valid
  intro output next step' hvalid
  have ends := (runScriptStep_continued step').2
  cases snapshot : ctx.connection.state.snapshot with
  | none =>
    obtain ⟨failed, -, nextEq⟩ := runScriptStep_commit_idle found snapshot step'
    exact success output next (by simp [failed, snapshot]) ends (by simp [Model.Connection.afterCommit, snapshot, nextEq])
      hvalid
  | some original =>
    obtain ⟨noError, -, nextEq⟩ := runScriptStep_commit_active found snapshot step'
    exact success output next (by simp [noError, snapshot]) ends (by simp [Model.Connection.afterCommit, snapshot, nextEq])
      hvalid

/-- The deleted law {lit}`Sql.check_send_setting`. For every context, statement, values and post, with a valid connection in the context: the program that
sends the statement checks the post when these premises hold.
* {lit}`found`: the statement resolves from the connection to a setting {lit}`setting` at the value {lit}`on`.
* {lit}`success`: for every output that is not an error and does not end the run, and for the connection with
  the setting at the value ({name}`Model.Connection.set`): if that connection is valid, the post holds for the
  list of that one output and the context after it.
In plain words, a setting changes the setting and nothing else, whether or not a transaction is open. Proof
sketch: as {name}`Sql.check_send_dropPlain`, with {name}`Model.ReplacedControls.runScriptStep_setting_continues` and
{name}`Model.ReplacedControls.runScriptStep_setting`. -/
theorem Sql.check_send_setting {ctx : ExecutionContext} {statement : Syntax.Statement}
    {values : List Value} {setting : Syntax.PragmaSetting} {«on» : Bool} {after : ResolveState}
    {post : List Output → ExecutionContext → Prop}
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState statement = .ok (.setting setting «on», after))
    (success : ∀ (output : Output) (next : Connection), output.isError = false → output.endsRun = false →
      next = ctx.connection.set «on» setting →
      next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  obtain ⟨output, next, step⟩ := runScriptStep_setting_continues (parameters := values) (clock := ctx.clock)
    (index := ctx.index) found
  refine Sql.check_send_of_step (fun _ _ resolved => by
      obtain rfl := (Prod.mk.inj (Except.ok.inj (resolved.symm.trans found))).1
      rfl) ⟨output, next, [], step⟩
    (fun _ _ _ step => runScriptStep_ne_oneOf_of_not_query found (by intro _ _ same; cases same) step) ?_ valid
  intro output next step' hvalid
  obtain ⟨noError, -, nextEq⟩ := runScriptStep_setting found step'
  exact success output next noError (runScriptStep_continued step').2 nextEq hvalid

#print axioms Sql.check_send_begin
#print axioms Sql.check_send_commit
#print axioms Sql.check_send_setting

end Belay.Sqlite.ReplacedControls
