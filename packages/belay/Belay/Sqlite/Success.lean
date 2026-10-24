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

/-- The program succeeds from this connection, clock and statement index:

* A pure program always succeeds.
* A statement that ends the run never succeeds.
* A continuing statement must have no error. Its continuation must succeed on the actual
  output. If the output is {name}`Output.oneOf`, the continuation must also succeed on
  {name}`Output.rows` for every listed result; an empty list adds no such requirement.

Every continuation uses the next statement index and the exact connection left by the
statement. This primitive also accepts incomplete environments. Use {lit}`Succeeds` for a
claim over every database and complete environment. -/
def Sql.SucceedsFrom {α : Type} (clock : Option Clock) (index : Nat) (connection : Connection) : Sql α → Prop
  | .pure _ => True
  | .exec statement values rest =>
    match runScriptStep runContext clock index connection statement values with
    | .ended _ => False
    | .continued output next =>
      output.isError = false ∧ (rest output).SucceedsFrom clock (index + 1) next ∧
        match output with
        | .oneOf results => ∀ rows ∈ results, (rest (.rows rows)).SucceedsFrom clock (index + 1) next
        | _ => True

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

/-- Success from a fixed connection is decidable: each statement has one actual output and
finitely many listed alternatives. Use {lit}`decide +kernel` on a concrete program and state. -/
instance Sql.decidableSucceedsFrom {α : Type} (clock : Option Clock) (index : Nat)
    (connection : Connection) (program : Sql α) : Decidable (program.SucceedsFrom clock index connection) :=
  match program with
  | .pure _ => isTrue True.intro
  | .exec statement values rest => by
      simp only [Sql.SucceedsFrom]
      split
      · infer_instance
      · rename_i output next step
        letI (seen : Output) := Sql.decidableSucceedsFrom clock (index + 1) next (rest seen)
        cases output <;> infer_instance
termination_by structural program

end Belay.Sqlite
