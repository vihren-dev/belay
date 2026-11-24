import Belay.Sqlite.Programs.Reasoning.SendSingleStep

set_option doc.verso true

/-! The send of one statement through a kind rule (statement rule pilot). A kind rule of the model, such as
{lit}`runScriptStep_createTable_eq`, gives the step of every statement that resolves to its kind as an equation
{lit}`runScriptStep … = result`. The theorem {lit}`Sql.check_send_of_rule` of this module turns such an equation into
the check of a program that sends the statement. It does not depend on the kind: the cases of {lit}`result` carry
all that is special to the kind, and a proof, or {lit}`sql_run`, reads them by a case split on {lit}`result`. -/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- What a program that sends one statement asks of one continuing case of the step, for the post and the
context: for every execution of the case (the output and the next connection first, then each further
execution), if the next connection of the execution is valid, then the post holds for the list of the output and
the context after it, and, when the output is a choice between results, also for each result
({name}`OutputChoice.Checked`). A connection is valid when its state holds {name}`SqlState.Holds` for
{lean}`Database.Valid Profile.pinned`: its database is valid, and, when the state has the snapshot of an open
transaction, the snapshot is valid too; a state without a snapshot asks only for the database. An execution whose
next connection is not valid requires nothing. -/
def Sql.SendReached (post : List Output → ExecutionContext → Prop) (ctx : ExecutionContext) (output : Output)
    (next : Connection) (others : List StatementExecution) : Prop :=
  ∀ found ∈ (RunStep.continued output next others).executions,
    found.next.state.Holds (Database.Valid Profile.pinned) →
      OutputChoice.Checked (fun selected => post [selected] (ctx.next selected found.next)) found.output

/-- The bridge from a kind rule to the check of a send. For every context, statement, values, post and step
{lit}`result`: the program that sends the one statement checks the post at the context when all of these hold.
- {lit}`rule`: the step of the statement at the context is {lit}`result`. A kind rule gives this equation.
- {lit}`valid`: the state of the connection of the context holds {name}`SqlState.Holds` for
  {lean}`Database.Valid Profile.pinned`: its database is valid, and, when the state has the snapshot of an open
  transaction, the snapshot is valid too.
- {lit}`modeled`: {lit}`result` continues ({name}`RunStep.continues`).
- {lit}`reached`: every continuing case of {lit}`result` ({name}`RunStep.Continuing`) meets
  {name}`Sql.SendReached` for the post and the context.
The theorem has no premise about the kind of the statement, and it does not assume one execution or an output
that is not a choice. Proof sketch: {name}`Sql.check_exec` with the rule; {lit}`modeled` excludes a step that ends,
and {name}`runScriptStep_valid` gives the validity of each next connection that {lit}`reached` asks for. -/
theorem Sql.check_send_of_rule {ctx : ExecutionContext} {statement : Syntax.Statement} {values : List Value}
    {post : List Output → ExecutionContext → Prop} {result : RunStep}
    (rule : runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = result)
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned))
    (modeled : result.continues = true)
    (reached : result.Continuing (Sql.SendReached post ctx)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  have kept := runScriptStep_valid (profile := Profile.pinned) runContext ctx.clock ctx.index statement values rfl rfl
    valid
  unfold send
  simp only [sendStatements]
  rw [Sql.check_exec, rule]
  rw [rule] at kept
  cases result with
  | ended reason => simp [RunStep.continues] at modeled
  | continued output next others =>
    intro found member
    obtain ⟨raw, alternatives⟩ := reached found member (kept found member)
    obtain ⟨output, next⟩ := found
    refine ⟨by simpa [Sql.map, Sql.check_pure] using raw, ?_⟩
    cases output with
    | oneOf results => exact fun rows listed => by simpa [Sql.map, Sql.check_pure] using alternatives rows listed
    | done _ | rows _ | error _ | unmodeled _ => trivial

/-- For every postcondition, context and continued step with an output, next connection and further executions,
suppose that for every member of its {name}`RunStep.executions` whose next state satisfies
{name}`SqlState.Holds` for {lean}`Database.Valid Profile.pinned`, and for each output selected from that
execution by {name}`OutputChoice`, the postcondition holds for the singleton selected output and the context
advanced with that output and the execution's next connection. Then the continued step satisfies
{name}`RunStep.Continuing` for {name}`Sql.SendReached` at that postcondition and context.
Proof sketch: use the universal form of {name}`OutputChoice.Checked` for each valid execution. -/
theorem Sql.sendReached_each {post : List Output → ExecutionContext → Prop} {ctx : ExecutionContext}
    {output : Output} {next : Connection} {others : List StatementExecution}
    (holds : ∀ execution ∈ (RunStep.continued output next others).executions,
      execution.next.state.Holds (Database.Valid Profile.pinned) →
      ∀ selected, OutputChoice execution.output selected → post [selected] (ctx.next selected execution.next)) :
    (RunStep.continued output next others).Continuing (Sql.SendReached post ctx) := by
  intro execution member valid
  exact (OutputChoice.forall_iff _ _).1 (holds execution member valid)

/-- For every post, context, output and next connection: if the output is no choice between results, and the post
holds for the list of the output and the context after it whenever the state of the next connection holds
{name}`SqlState.Holds` for {lean}`Database.Valid Profile.pinned` (a valid database and, when the state has the
snapshot of an open transaction, a valid snapshot), then the step that continues with that output,
that connection and no further execution meets {name}`Sql.SendReached` ({name}`RunStep.Continuing`). Proof sketch:
the step has one execution, and {name}`OutputChoice.Checked` of an output that is no choice is the post for it. -/
theorem Sql.sendReached_single {post : List Output → ExecutionContext → Prop} {ctx : ExecutionContext}
    {output : Output} {next : Connection} (plain : ∀ results, output ≠ .oneOf results)
    (holds : next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next)) :
    (RunStep.continued output next []).Continuing (Sql.SendReached post ctx) := by
  intro found member valid
  simp only [RunStep.executions, List.mem_singleton] at member
  subst member
  refine ⟨holds valid, ?_⟩
  cases output with
  | oneOf results => exact absurd rfl (plain results)
  | done _ | rows _ | error _ | unmodeled _ => trivial

/-- For every admitted database and environment: the connection of the fresh start satisfies the validity
condition that the step rules ask of the connection of their context. In plain words, a run that starts from
an admitted database starts valid, and it has no open transaction. Proof sketch: the database of the start is
the admitted database; the start has no snapshot. -/
theorem ExecutionContext.initial_holds_valid (db : Database) (env : Env) :
    (ExecutionContext.initial db env).connection.state.Holds (Database.Valid Profile.pinned) :=
  ⟨db.valid, fun _ same => by simp [ExecutionContext.initial, Database.Raw.connection] at same⟩

end Belay.Sqlite
