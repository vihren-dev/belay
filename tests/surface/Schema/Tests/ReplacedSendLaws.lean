import ReplacedFailureFrames
import ReplacedGeneralSend
import ReplacedStepLaws
import Belay.Sqlite.Programs.Scripts.KindRuleSend

/-! A fixture module of {lit}`tests/surface_schema_script_test.py` (statement rule pilot, "No capability loss"). The
pilot deleted three surface rules for a program that sends one CREATE TABLE or one plain INSERT. Each theorem of
this module has the name and the statement of one deleted rule, copied from the revision before the pilot with its
binders and premises, and proves it from the rules that remain: the bridge {name}`Sql.check_send_of_rule` with the
kind rule of CREATE TABLE, and {name}`ReplacedGeneral.Sql.check_send_of_step` with the model laws of
{lit}`ReplacedStepLaws`, which the kind rule of plain INSERT proves. When a theorem does not compile, the new form
has lost the fact. -/

set_option doc.verso true

open Belay.Sqlite.ReplacedFrames

namespace Belay.Sqlite.ReplacedSendLaws
open Belay.Sqlite Model

/-- The deleted rule {lit}`Sql.check_send_createTable`. For every context, statement, values and post, with a
valid connection in the context: the program that sends the statement checks the post when these premises hold.
* {lit}`found`: the statement resolves from the connection to CREATE TABLE at position {lit}`target`.
* {lit}`success`: for every output that is not an error and does not end the run, and for the connection with
  the new table at the end of the catalog and an empty row list at the end of the rows
  ({name}`Model.Connection.withDatabase`): if that connection is valid, the post holds for the list of that
  one output and the context after it.
Proof sketch: {name}`step_guards_hold` selects the branch of {name}`runScriptStep_createTable_eq` that continues,
and {name}`Sql.check_send_of_rule` with {name}`Sql.sendReached_single` leaves the premise {lit}`success`. -/
theorem Sql.check_send_createTable {ctx : ExecutionContext} {statement : Syntax.Statement}
    {values : List Value} {target : Nat} {name : Identifier} {table : CatalogTable} {after : ResolveState}
    {post : List Output → ExecutionContext → Prop}
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState statement =
      .ok (.createTable target name table, after))
    (success : ∀ (output : Output) (next : Connection), output.isError = false → output.endsRun = false →
      next = ctx.connection.withDatabase
        ({ catalog := ctx.connection.state.database.catalog.createTable name table,
           rows := ctx.connection.state.database.rows ++ [[]] } : Model.Database) →
      next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  have guards := step_guards_hold found rfl valid.1
  simp only [Resolved.Statement.StepGuards] at guards
  have rule := runScriptStep_createTable_eq (clock := ctx.clock) (index := ctx.index) (parameters := values) found
  simp only [guards, and_self, ↓reduceIte] at rule
  exact Sql.check_send_of_rule rule valid rfl
    (Sql.sendReached_single (fun _ same => by cases same) (success _ _ rfl rfl rfl))

/-- The deleted rule {lit}`Sql.check_send_plainInsert`. For every context {lit}`ctx`, statement, values and post,
with a valid connection in {lit}`ctx`: the program that sends the statement checks the post at {lit}`ctx` if these
premises hold.
* {lit}`found`: the statement resolves from the connection of {lit}`ctx` to a plain insert on position {lit}`target`.
* {lit}`present`: that position holds a table.
* {lit}`modeled`: the model runs the statement at {lit}`ctx` to a step that continues.
* {lit}`success`: for every output that is not an error and does not end the run, for every clock value that the
  statement reads at the index of {lit}`ctx`, and for every connection that is {name}`Model.Connection.afterWrite`
  with the database in which the target holds the rows that {name}`LiteralData.inserted` gives, and with the counts
  of the statement for that clock value: if that connection is valid, the post holds for the list of that one
  output and the context after it.
* {lit}`failure`: for every output that is an error and does not end the run, for every integer taken as the clock
  value, and for every connection that is {name}`Model.Connection.afterWrite` with the unchanged database and the
  counts of the statement for that value: if that connection is valid, the post holds for the list of that one
  output and the context after it.
Proof sketch: {name}`ReplacedGeneral.Sql.check_send_of_step`; {name}`runScriptStep_effect` and
{name}`ReplacedStepLaws.plainInsert_database` give the connection after a success, and
{name}`runScriptStep_plainWrite_failed` gives it after a failure. -/
theorem Sql.check_send_plainInsert {ctx : ExecutionContext} {statement : Syntax.Statement}
    {values : List Value} {target : Nat} {cells : List (List Resolved.Cell)} {after : ResolveState}
    {table : Table} {post : List Output → ExecutionContext → Prop}
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState statement =
      .ok (.insert target cells [] [] none, after))
    (present : ctx.connection.state.database.table target = some table)
    (modeled : ∃ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others)
    (success : ∀ (output : Output) (value : Int) (next : Connection), output.isError = false → output.endsRun = false →
      statementClock ctx.clock ctx.index (.insert target cells [] [] none) = some value →
      next = ctx.connection.afterWrite (ctx.connection.state.database.setRows target
        (LiteralData.inserted table (Resolved.rowsAt (Resolved.statementContext value
          (ctx.connection.state.counters.view (Resolved.Statement.insert target cells [] [] none).counterReads)
          values ctx.connection.state.database []) table.shape.columns cells)).rows)
        (ctx.connection.state.statementRun value values (.insert target cells [] [] none)).counts →
      next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next))
    (failure : ∀ (output : Output) (value : Int) (next : Connection), output.isError = true → output.endsRun = false →
      next = ctx.connection.afterWrite ctx.connection.state.database
        (ctx.connection.state.statementRun value values (.insert target cells [] [] none)).counts →
      next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  refine ReplacedGeneral.Sql.check_send_of_step (fun _ _ resolved => by
      obtain rfl := (Prod.mk.inj (Except.ok.inj (resolved.symm.trans found))).1
      rfl) modeled
    (fun _ _ _ step => runScriptStep_ne_oneOf_of_not_query found (fun _ _ same => by cases same) step) ?_ valid
  intro output next step reachedValid
  have ends := (runScriptStep_continued step).2
  cases noError : output.isError
  · obtain ⟨value, database, timed, effect, nextIs⟩ :=
      runScriptStep_effect found (by simp [Resolved.Statement.isControl]) step noError
    obtain ⟨value', timed', databaseIs⟩ := ReplacedStepLaws.plainInsert_database found present step noError
    obtain rfl : value' = value := Option.some.inj (timed'.symm.trans timed)
    subst nextIs
    simp only at databaseIs
    subst databaseIs
    exact success output value' _ noError ends timed' rfl reachedValid
  · obtain ⟨value, rfl⟩ := runScriptStep_plainWrite_failed found rfl step noError
    exact failure output value _ noError ends rfl reachedValid

/-- The deleted rule {lit}`Sql.ifOk_send_plainInsert`. Take a database, an environment (it need not be complete), a
plain insert that resolves from the initial connection and is modeled, and a post. The premise {lit}`reached` is
about every clock value, output list and final context. It requires the post for that output list and that context
when these three conditions hold:

* The database of the context is the given database with the new rows for that clock value appended to the target
  table in order.
* That database is valid.
* No output of the context is an error or ends the run.

The output list is independent of the outputs of the context.
Under this premise, a program that sends the insert satisfies {lit}`Sql.ifOk` of the post at its fresh start. That
is, every branch stays modeled, and only a branch whose outputs have no error must satisfy the post. Proof sketch:
{name}`ReplacedGeneral.check_send_single_of_step` with the step of the model; {name}`ReplacedStepLaws.plainInsert_database` gives
the database, {name}`runScriptStep_valid` its validity, and {name}`runScriptStep_ne_oneOf_of_not_query` rules out a
choice. -/
theorem Sql.ifOk_send_plainInsert {db : Database} {env : Env} {statement : Syntax.Statement}
    {values : List Value} {target : Nat} {cells : List (List Resolved.Cell)} {after : ResolveState}
    {table : Table}
    (found : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.insert target cells [] [] none, after))
    (present : db.raw.table target = some table)
    (modeled : ∃ output next others, runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
      statement values = .continued output next others)
    {post : List Output → ExecutionContext → Prop}
    (reached : ∀ (value : Int) (outputs : List Output) (final : ExecutionContext),
      final.connection.state.database = db.raw.setRows target
        (LiteralData.inserted table (Resolved.rowsAt (Resolved.statementContext value
          ((db.raw.connection env.counters).state.counters.view
            (Resolved.Statement.insert target cells [] [] none).counterReads)
          values db.raw []) table.shape.columns cells)).rows →
      final.connection.state.database.Valid Profile.pinned → final.outputs.allOk = true →
      post outputs final) :
    (send ⟨[(statement, values)]⟩).ifOk post (ExecutionContext.initial db env) := by
  obtain ⟨output, next, others, step⟩ := modeled
  refine (ReplacedGeneral.check_send_single_of_step (state := ExecutionContext.initial db env) step
    (fun _ _ resolved => by
      obtain rfl := (Prod.mk.inj (Except.ok.inj (resolved.symm.trans found))).1
      rfl)
    (runScriptStep_ne_oneOf_of_not_query found (fun _ _ same => by cases same) step)).2 ?_
  intro allOk
  have noError : output.isError = false := by
    simp [ExecutionContext.next, List.allOk] at allOk
    exact allOk.2.1
  obtain ⟨value, -, effect⟩ := ReplacedStepLaws.plainInsert_database found present step noError
  have start : (db.raw.connection env.counters).state.Holds (Database.Valid Profile.pinned) :=
    ExecutionContext.initial_holds_valid db env
  have valid : next.state.Holds (Database.Valid Profile.pinned) :=
    runScriptStep_valid (profile := Profile.pinned) runContext env.clock 0 statement values rfl rfl start
      { output, next } (by rw [step]; simp [RunStep.executions])
  exact reached value [output] _ effect valid.1 allOk

#print axioms Sql.check_send_createTable
#print axioms Sql.check_send_plainInsert
#print axioms Sql.ifOk_send_plainInsert

end Belay.Sqlite.ReplacedSendLaws
