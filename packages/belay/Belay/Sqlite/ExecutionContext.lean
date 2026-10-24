import Belay.Sqlite.ProgramBindLaws

set_option doc.verso true

namespace Belay.Sqlite
open Model

/-- Inputs and accumulated observations for a program proof. For a fresh surface run,
use {lit}`ExecutionContext.initial`; keep this whole context when composing programs. -/
structure ExecutionContext where
  /-- The statement-indexed clock shared by all steps; none permits no clock reads. -/
  clock : Option Clock
  /-- The index of the next statement, including steps before this program. -/
  index : Nat
  /-- The full connection, including counters, settings and any transaction snapshot. -/
  connection : Connection
  /-- Outputs before this program; use the empty list for a fresh run. -/
  outputs : List Output := []

/-- Append a complete run to a proof context. A stopping step counts as an executed step;
the existing clock is preserved. This operation does not execute SQL. -/
def ExecutionContext.finish {α : Type} (state : ExecutionContext) (result : SqlRun α) : ExecutionContext :=
  { state with
    index := state.index + result.outputs.length,
    connection := result.connection, outputs := state.outputs ++ result.outputs }

/-- Advance by one chosen output and the actual next connection. Use this context for
that output's continuation; it retains the original clock and every earlier output. -/
def ExecutionContext.next (state : ExecutionContext) (output : Output) (connection : Connection) : ExecutionContext :=
  { state with index := state.index + 1, connection, outputs := state.outputs ++ [output] }

/-- For every chosen output and later result, finishing their prefixed result equals
advancing once and then finishing the later result. Proof sketch: append and addition laws. -/
theorem ExecutionContext.finish_prepend {α : Type} (state : ExecutionContext) (output : Output)
    (connection : Connection) (result : SqlRun α) :
    state.finish { result with outputs := output :: result.outputs } =
      (state.next output connection).finish result := by
  simp [ExecutionContext.finish, ExecutionContext.next, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The proof context of a fresh surface run: the supplied environment, index zero,
a new connection to the bundled database, and an empty output trace. -/
def ExecutionContext.initial (db : Database) (env : Env) : ExecutionContext :=
  ⟨env.clock, 0, db.raw.connection env.counters, []⟩

/-- For every prefix result and every following result, finishing their
concatenated result equals finishing them in sequence. The clock is unchanged.
Proof sketch: list append and natural-number addition are associative. -/
theorem ExecutionContext.finish_append {α β : Type} (state : ExecutionContext)
    (first : SqlRun α) (second : SqlRun β) :
    state.finish { second with outputs := first.outputs ++ second.outputs } =
      (state.finish first).finish second := by
  simp [ExecutionContext.finish, List.length_append, List.append_assoc, Nat.add_assoc]

end Belay.Sqlite
