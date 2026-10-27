import Belay.Sqlite.Success
import Belay.Sqlite.SendStatementsBranches

set_option doc.verso true

/-! Success of a sent script along a property of its steps (ADR 0017, S6). A script with an INSERT from a query
has several executions at that step, so its success is a claim about all of them ({lit}`Sql.SucceedsFrom`).
This module shows that a script succeeds when, at every position, the property holds for the connection and the
step continues, and every execution of the step has no error output and satisfies the property at the next
position. It is the success counterpart of {lit}`sendStatements_branch_invariant`. -/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every condition on outputs and the two ways to state it for one output: the conditions of
{name}`Sql.ExecutionSucceeds` for two continuations that agree on every output are equivalent. Proof sketch: unfold
and split on the output. -/
theorem Sql.executionSucceeds_congr {first second : Output → Prop} (same : ∀ seen, first seen ↔ second seen)
    (output : Output) : Sql.ExecutionSucceeds first output ↔ Sql.ExecutionSucceeds second output := by
  unfold Sql.ExecutionSucceeds
  cases output <;> simp [same]

/-- For every function and program: the program with its value mapped through the function succeeds from a
context exactly when the program does. In plain words, changing the value that a program returns does not change
whether it succeeds. Proof sketch: induction on the program; the mapped program sends the same statements. -/
theorem Sql.succeedsFrom_map {α β : Type} (function : α → β) (program : Sql α) :
    ∀ (clock : Option Clock) (index : Nat) (connection : Connection),
      (program.map function).SucceedsFrom clock index connection ↔ program.SucceedsFrom clock index connection := by
  induction program with
  | pure value => intro clock index connection; simp [Sql.map, Sql.SucceedsFrom]
  | exec statement values rest later =>
    intro clock index connection
    simp only [Sql.map, Sql.SucceedsFrom]
    cases runScriptStep runContext clock index connection statement values with
    | ended reason => exact Iff.rfl
    | continued output next others =>
      exact forall_congr' fun found => forall_congr' fun _ =>
        Sql.executionSucceeds_congr (fun seen => later seen clock (index + 1) found.next) _

/-- For every list of statements and every property {lit}`Inv` of a position in the list and a connection: the
sent statements succeed from a connection that is valid and has the property at position 0 if, for every position
{lit}`n` in the list, every index and every valid connection where the property holds at {lit}`n`:
* the step of statement {lit}`n` continues, and
* every execution of the step has no error output and its next connection has the property at {lit}`n + 1`.

In plain words, success follows from a property that each step keeps together with the fact that each step
continues without an error, in all of its executions. The hypothesis is about every index and every connection with
the property, so it holds for the connection of every branch. Proof sketch: induction on the statements. The
outputs of a continuation do not matter ({name}`Sql.succeedsFrom_map`), so the condition of
{name}`Sql.ExecutionSucceeds` reduces to the absence of an error and the success of the rest from the next
connection, which is valid ({name}`runScriptStep_valid`) and has the property shifted by one. -/
theorem sendStatements_succeedsFrom (statements : List (Syntax.Statement × List Value)) :
    ∀ (Inv : Nat → Connection → Prop) (clock : Option Clock) (index : Nat) (connection : Connection),
      connection.state.Holds (Database.Valid Profile.pinned) → Inv 0 connection →
      (∀ (n : Nat) (inList : n < statements.length) (index : Nat) (connection : Connection),
        connection.state.Holds (Database.Valid Profile.pinned) → Inv n connection →
        ∃ output next others, runScriptStep runContext clock index connection statements[n].1 statements[n].2 =
          .continued output next others ∧ ∀ found ∈ (RunStep.continued output next others).executions,
          found.output.isError = false ∧ Inv (n + 1) found.next) →
      (sendStatements statements).SucceedsFrom clock index connection := by
  induction statements with
  | nil => intro Inv clock index connection _ _ _; exact True.intro
  | cons head rest later =>
    rcases head with ⟨statement, values⟩
    intro Inv clock index connection valid start advance
    obtain ⟨output, next, others, shown, all⟩ := advance 0 (Nat.succ_pos _) index connection valid start
    have step : runScriptStep runContext clock index connection statement values = .continued output next others :=
      shown
    simp only [sendStatements, Sql.SucceedsFrom, step]
    intro found member
    obtain ⟨noError, reached⟩ := all found member
    have foundValid := runScriptStep_valid (profile := Profile.pinned) runContext clock index statement values rfl rfl
      valid found (by rw [step]; exact member)
    have tail : ∀ seen, ((sendStatements rest).map (seen :: ·)).SucceedsFrom clock (index + 1) found.next :=
      fun seen => (Sql.succeedsFrom_map _ _ _ _ _).mpr
        (later (fun n => Inv (n + 1)) clock (index + 1) found.next foundValid reached
          (fun n inList index' connection' valid' holds' => advance (n + 1) (Nat.succ_lt_succ inList) index'
            connection' valid' holds'))
    refine ⟨noError, tail _, ?_⟩
    cases found.output <;> simp [tail]

end Belay.Sqlite
