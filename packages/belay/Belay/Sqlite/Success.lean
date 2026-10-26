import Belay.Sqlite.ProgramRun
import Belay.Sqlite.ProgramQueries

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- The environment supplies a clock and knows each of the three counters. Their values are
unrestricted. For example, {lean}`{ Env.atTime 0 with counters := Counters.newConnection }`
is complete. Success quantifies over these environments so that a missing input does not
make an otherwise modeled statement stop. -/
def Env.Complete (env : Env) : Prop :=
  env.clock.isSome = true ∧ env.counters.changes.isSome = true ∧
    env.counters.totalChanges.isSome = true ∧ env.counters.lastInsertRowid.isSome = true

/-- The condition on one execution of a continuing statement: its output is no error, and the
continuation succeeds on that output. If the output is {name}`Output.oneOf`, the continuation must also
succeed on {name}`Output.rows` for every listed result; an empty list adds no such requirement.
For example, the output {lean}`Output.done 1` needs only that the continuation succeeds on it. -/
def Sql.ExecutionSucceeds (continuation : Output → Prop) (output : Output) : Prop :=
  output.isError = false ∧ continuation output ∧
    match output with
    | .oneOf results => ∀ rows ∈ results, continuation (.rows rows)
    | .done _ | .rows _ | .error _ | .unmodeled _ => True

/-- The program succeeds from this connection, clock and statement index:

* A pure program always succeeds.
* A statement that ends the run never succeeds.
* A continuing statement succeeds when each of its executions
  ({name}`RunStep.executions`) does ({name}`Sql.ExecutionSucceeds`): it has no error, and the
  continuation, from the connection of that execution, succeeds on its output, and on every listed
  result if the output is {name}`Output.oneOf`.

Every continuation uses the next statement index and the exact connection left by the
execution. This primitive also accepts incomplete environments. Use {lit}`Succeeds` for a
claim over every database and complete environment. -/
def Sql.SucceedsFrom {α : Type} (clock : Option Clock) (index : Nat) (connection : Connection) : Sql α → Prop
  | .pure _ => True
  | .exec statement values rest =>
    match runScriptStep runContext clock index connection statement values with
    | .ended _ => False
    | .continued output next others =>
      ∀ found ∈ (RunStep.continued output next others).executions,
        Sql.ExecutionSucceeds (fun seen => (rest seen).SucceedsFrom clock (index + 1) found.next) found.output

/-- For a continuing statement, success is the condition on its one execution, the model's own, with
the output and connection of the step. Every statement that the model describes has one execution.
Proof sketch: the executions of the step are that one execution
({name}`runScriptStep_executions`). -/
theorem Sql.succeedsFrom_continued {α : Type} {clock : Option Clock} {index : Nat} {connection : Connection}
    {statement values} {rest : Output → Sql α} {output next others}
    (step : runScriptStep runContext clock index connection statement values = .continued output next others) :
    (Sql.exec statement values rest).SucceedsFrom clock index connection ↔
      Sql.ExecutionSucceeds (fun seen => (rest seen).SucceedsFrom clock (index + 1) next) output := by
  simp only [Sql.SucceedsFrom, step, runScriptStep_executions step, List.mem_singleton, forall_eq]

/-- For every database satisfying the arbitrary predicate, and every complete environment,
the script or program succeeds on every branch ({name}`Sql.SucceedsFrom`). A predicate that
no database satisfies requires nothing. For example, use {lean}`fun _ : Database => True`
for an unconditional claim, or a predicate about the catalog when SQL cannot express it.
The {lit}`succeeds where` notation supplies a query predicate as a convenience. -/
def Succeeds {σ α : Type} [Runnable σ α] (program : σ) (predicate : Database → Prop) : Prop :=
  ∀ db, predicate db → ∀ env : Env, env.Complete →
    (Runnable.toSql program).SucceedsFrom env.clock 0 (db.raw.connection env.counters)

/-- For every script or program and predicates, success under the first predicate implies
success under any predicate that implies it. Proof sketch: apply the given implication at
each database, then reuse the same complete environment and branch proof. -/
theorem Succeeds.mono {σ α : Type} [Runnable σ α] {program : σ} {first second : Database → Prop}
    (success : Succeeds program first) (implies : ∀ db, second db → first db) :
    Succeeds program second := fun db holds env complete => success db (implies db holds) env complete

/-- For every value and database predicate, a pure program succeeds: it sends no statement.
Proof sketch: its branch predicate is {lean}`True` in every environment. -/
theorem Succeeds.pure {α : Type} (value : α) (predicate : Database → Prop) :
    Succeeds (Sql.pure value) predicate := fun _ _ _ _ => True.intro

/-- For every script and predicate, sending the script succeeds exactly when the script
succeeds. Proof sketch: the {name}`Runnable` instance for scripts is {name}`send`. -/
theorem Succeeds.send_iff (script : Script) (predicate : Database → Prop) :
    Succeeds (send script) predicate ↔ Succeeds script predicate := Iff.rfl

/-- For every program and predicate, one database satisfying the predicate and one complete
environment where a branch fails refute success. Proof sketch: instantiate the universal
success claim with that database and environment. -/
theorem Succeeds.not_of_failure {α : Type} {program : Sql α} {predicate : Database → Prop}
    {db : Database} {env : Env} (holds : predicate db) (complete : env.Complete)
    (failure : ¬ program.SucceedsFrom env.clock 0 (db.raw.connection env.counters)) :
    ¬ Succeeds program predicate := fun success => failure (success db holds env complete)

/-- The condition {name}`Sql.ExecutionSucceeds` is decidable when the continuation is. -/
instance Sql.decidableExecutionSucceeds (continuation : Output → Prop) [DecidablePred continuation]
    (output : Output) : Decidable (Sql.ExecutionSucceeds continuation output) := by
  unfold Sql.ExecutionSucceeds
  cases output <;> dsimp <;> infer_instance

/-- Success from a fixed connection is decidable: each statement has finitely many executions, each
with one actual output and finitely many listed alternatives. Use {lit}`decide +kernel` on a concrete
program and state. -/
instance Sql.decidableSucceedsFrom {α : Type} (clock : Option Clock) (index : Nat)
    (connection : Connection) (program : Sql α) : Decidable (program.SucceedsFrom clock index connection) :=
  match program with
  | .pure _ => isTrue True.intro
  | .exec statement values rest => by
      simp only [Sql.SucceedsFrom]
      split
      · infer_instance
      · rename_i output next others step
        letI (found : StatementExecution) (seen : Output) :=
          Sql.decidableSucceedsFrom clock (index + 1) found.next (rest seen)
        exact List.decidableBAll _ _
termination_by structural program

end Belay.Sqlite
