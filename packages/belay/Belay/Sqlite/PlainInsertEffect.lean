import Belay.Sqlite.ExecutionStep
import Belay.Sqlite.ExecutionSuccess
import Belay.Sqlite.ProgramQueries

set_option doc.verso true

/-!
The effect of one plain INSERT in a fresh run (ADR 0017, S6). A plain INSERT is a resolved insert
without a RETURNING clause, subqueries or trigger and foreign-key rules. The module shows what
the model's run of such a statement stores and what a program that sends it checks. A universal
claim about an INSERT then needs only the rows that the statement adds to the table, not the
engine.
-/

namespace Belay.Sqlite.Model

/-- For every database, target, keys, table, supplied rows and result table: if the write of
the result succeeds, it gives the database with the rows of the result stored at the target.
Proof sketch: split the data-domain check and the checked write; each failing branch is an error,
and the successful branch stores the rows. -/
theorem insertOutcome_ok {database : Model.Database} {target : Nat} {keys : List UniqueKey}
    {table : Table} {rows : List (List Value)} {result : Table} {after : Model.Database}
    (ok : insertOutcome database target keys table rows result = .ok after) :
    after = database.setRows target result.rows := by
  unfold insertOutcome at ok
  split at ok
  · dsimp only at ok
    split at ok <;> cases ok
  · unfold checkedWrite at ok
    split at ok
    · cases ok; rfl
    · cases ok

/-- For every connection, plain insert and error-free step that continues: the next connection
has the database with the rows that {lit}`LiteralData.inserted` gives, stored at the target. The
statement context is that of the clock value of the step. Proof sketch:
{name}`runScriptStep_effect` gives the effect of the run, and {name}`insertOutcome_ok` reads it. -/
theorem plainInsert_database {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {target : Nat} {cells : List (List Resolved.Cell)} {after : ResolveState} {table : Table}
    (found : resolveStatement runContext connection.resolveState statement =
      .ok (.insert target cells [] [] none, after))
    (present : connection.state.database.table target = some table)
    (step : runScriptStep runContext clock index connection statement parameters = .continued output next)
    (noError : output.isError = false) :
    ∃ value : Int, statementClock clock index (.insert target cells [] [] none) = some value ∧
      next.state.database = connection.state.database.setRows target
        (LiteralData.inserted table (Resolved.rowsAt (Resolved.statementContext value
          (connection.state.counters.view (Resolved.Statement.insert target cells [] [] none).counterReads)
          parameters connection.state.database []) table.shape.columns cells)).rows := by
  obtain ⟨value, database, timed, effect, nextEq⟩ :=
    runScriptStep_effect found (by simp [Resolved.Statement.isControl]) step noError
  refine ⟨value, timed, ?_⟩
  simp only [SqlState.statementRun, runStatement, present, StatementRun.withKeys, Option.map_none] at effect
  rw [nextEq, insertOutcome_ok effect]

/-- For every clock, statement values, state, run, transition, target and rule fields: the
output of a step of an insert is never a choice between results. Only a query step gives one.
Proof sketch: unfold the output and split on the halt reason; every remaining case gives rows,
a done count, an error or an unmodeled stop. -/
theorem Output.ofStep_insert_ne_oneOf (clock : Int) (parameters : List Value) (before : SqlState)
    (run : StatementRun) (transition : SqlTransition) (target : Nat) (rows returning subqueries rules)
    (alternatives : List (List (List Value))) :
    Output.ofStep clock parameters (.insert target rows returning subqueries rules) before run transition ≠
      .oneOf alternatives := by
  unfold Output.ofStep
  rcases haltError transition with _ | failure
  · dsimp only
    split
    · split <;> simp
    · simp
  · cases failure <;> simp

/-- Whether a step of a statement continues the run. The Boolean form lets a closed check compute it
for every clock and every counter, which an existence statement does not. -/
def RunStep.continues : RunStep → Bool
  | .continued .. => true
  | .ended _ => false

/-- For every step, it continues exactly when some output and next connection give it. Proof sketch:
case split on the step. -/
theorem RunStep.continues_iff {step : RunStep} :
    step.continues = true ↔ ∃ output next, step = .continued output next := by
  cases step <;> simp [RunStep.continues]

/-- For every connection, statement that resolves to an insert, and step that continues: the output
of the step is not a choice between results. Proof sketch: {name}`runScriptStep_ran` gives the output
as {name}`Output.ofStep` of the resolved statement, which {name}`Output.ofStep_insert_ne_oneOf`
treats. -/
theorem runScriptStep_insert_ne_oneOf {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {target : Nat}
    {cells : List (List Resolved.Cell)} {returning subqueries rules} {after : ResolveState}
    (found : resolveStatement runContext connection.resolveState statement =
      .ok (.insert target cells returning subqueries rules, after))
    (step : runScriptStep runContext clock index connection statement parameters = .continued output next)
    (alternatives : List (List (List Value))) : output ≠ .oneOf alternatives := by
  obtain ⟨resolved, later, value, same, -, -, -, outputEq, -⟩ := runScriptStep_ran step
  rw [found] at same
  cases same
  rw [outputEq]
  exact Output.ofStep_insert_ne_oneOf _ _ _ _ _ _ _ _ _ _ alternatives

end Belay.Sqlite.Model

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every post, context, statement, values and continuing step whose output is not a choice:
a program that sends the one statement checks the post exactly at the context after the step with
the one output. Proof sketch: {name}`Sql.check_exec` with the step; the output is not a choice, so
only the raw continuation remains. -/
theorem check_send_single_of_step {statement : Syntax.Statement} {values : List Value}
    {post : List Output → ExecutionContext → Prop} {state : ExecutionContext}
    {actual : Output} {connection : Connection}
    (step : runScriptStep runContext state.clock state.index state.connection statement values =
      .continued actual connection)
    (notChoice : ∀ alternatives, actual ≠ .oneOf alternatives) :
    (send ⟨[(statement, values)]⟩).check post state ↔ post [actual] (state.next actual connection) := by
  unfold send
  simp only [sendStatements]
  rw [Sql.check_exec, step]
  dsimp only
  cases actual with
  | oneOf alternatives => exact absurd rfl (notChoice alternatives)
  | done _ | rows _ | error _ | unmodeled _ =>
    simp [Sql.check_pure, Sql.map]

/-- For every database, complete environment, plain insert that resolves from the initial connection
and is modeled, and post: a program that sends the insert checks the post at its fresh start when
the post holds, for every error-free final context that sees the database with the inserted rows
and that database is valid. The rows are those of {name}`plainInsert_database` for the clock value
and the counters of the step. Only the reached database and the validity enter, so a claim about
the rows added by the statement needs no engine reasoning. Proof sketch:
{name}`check_send_single_of_step` with the step of the model; {name}`plainInsert_database` gives
the database, {name}`runScriptStep_valid` its validity, and {name}`runScriptStep_insert_ne_oneOf`
rules out a choice. -/
theorem Sql.ifOk_send_plainInsert {db : Database} {env : Env} {statement : Syntax.Statement}
    {values : List Value} {target : Nat} {cells : List (List Resolved.Cell)} {after : ResolveState}
    {table : Table}
    (found : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.insert target cells [] [] none, after))
    (present : db.raw.table target = some table)
    (modeled : ∃ output next, runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
      statement values = .continued output next)
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
  obtain ⟨output, next, step⟩ := modeled
  refine (check_send_single_of_step (state := ExecutionContext.initial db env) step
    (runScriptStep_insert_ne_oneOf found step)).2 ?_
  intro allOk
  have noError : output.isError = false := by
    simp [ExecutionContext.next, List.allOk] at allOk
    exact allOk.2.1
  obtain ⟨value, -, effect⟩ := plainInsert_database found present step noError
  have valid := runScriptStep_valid (profile := Profile.pinned) runContext env.clock 0 statement values rfl rfl
    ⟨db.valid, fun _ same => by simp [Database.Raw.connection] at same⟩ step
  exact reached value [output] _ effect valid.1 allOk

end Belay.Sqlite
