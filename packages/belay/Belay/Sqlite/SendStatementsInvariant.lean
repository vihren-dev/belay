import Belay.Sqlite.SendStatementsBranches
import Belay.Sqlite.ProgramQueries

set_option doc.verso true

/-! An invariant along the branches of a sent script (ADR 0017, S6). A script with an INSERT from a query can
reach different connections in different branches, so the connection of the model's run says nothing about
the other branches ({lit}`sendStatements_branch_shape`). A property that every execution of every step keeps
holds at the end of every branch that returns without an error. This is the way to state a fact about the
connection that a migration with such a statement reaches. -/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every output that a branch selects from an execution: if the selected output is no error, the output
of the execution is no error. Proof sketch: the selected output is the output itself, or a listed result of
a choice, and a choice is no error. -/
theorem OutputChoice.not_error {actual selected : Output} (choice : OutputChoice actual selected)
    (noError : selected.isError = false) : actual.isError = false := by
  rcases choice with rfl | choice
  · exact noError
  · cases actual <;> simp_all [Output.isError]

/-- For every list of statements and every property {lit}`Inv` of a position in the list and a connection:
if
* a branch of the sent statements returns a value and has only outputs that are no error and do not end the
  run ({name}`List.allOk`),
* the property holds at position 0 for the connection where the branch starts, and that connection is valid,
* and, for every position {lit}`n` in the list, every index and every connection where the property holds at
  {lit}`n` and the state holds {name}`SqlState.Holds` for {lean}`Database.Valid Profile.pinned`: the next
  connection of every execution of the step of statement {lit}`n` that has an output that is no error
  satisfies the property at {lit}`n + 1`,

then the property holds at the length of the list for the connection where the branch ends. In plain words, a
fact that each step keeps, whichever of its executions the branch takes, holds at the end of every branch that
succeeds. The statement says nothing about a branch that stops or has an error output, and nothing about the
index or the counters (the step premise holds for every index). Proof sketch: induction on the statements. A
stopping step has no value. After a continuing step, the branch takes an execution
({name}`Sql.branch_continued_executions_iff`) whose output is no error
({name}`OutputChoice.not_error`), the next connection is valid ({name}`runScriptStep_valid`) and the rest of
the branch is a branch of the remaining statements ({name}`Sql.branch_map_iff`), to which the induction
hypothesis applies with the property shifted by one position. -/
theorem sendStatements_branch_invariant (statements : List (Syntax.Statement × List Value)) :
    ∀ (Inv : Nat → Connection → Prop) (clock : Option Clock) (index : Nat) (connection : Connection)
      (result : SqlRun (List Output)),
      (sendStatements statements).Branch clock index connection result →
      result.value.isSome = true → result.outputs.allOk = true →
      connection.state.Holds (Database.Valid Profile.pinned) → Inv 0 connection →
      (∀ (n : Nat) (inList : n < statements.length) (index : Nat) (connection : Connection),
        connection.state.Holds (Database.Valid Profile.pinned) → Inv n connection →
        ∀ output next others, runScriptStep runContext clock index connection statements[n].1 statements[n].2 =
          .continued output next others → ∀ found ∈ (RunStep.continued output next others).executions,
          found.output.isError = false → Inv (n + 1) found.next) →
      Inv statements.length result.connection := by
  induction statements with
  | nil =>
    intro Inv clock index connection result branch _ _ _ start _
    obtain rfl := (Sql.branch_pure_iff _ _ _ _ _).mp branch
    exact start
  | cons head rest later =>
    rcases head with ⟨statement, values⟩
    intro Inv clock index connection result branch returned ok valid start advance
    cases step : runScriptStep runContext clock index connection statement values with
    | ended reason =>
      obtain rfl := (Sql.branch_stopped_iff (rest := fun output => (sendStatements rest).map (output :: ·)) step _).mp
        branch
      simp at returned
    | continued output next others =>
      obtain ⟨found, member, selected, tail, choice, tailBranch, rfl⟩ :=
        (Sql.branch_continued_executions_iff (rest := fun output => (sendStatements rest).map (output :: ·)) step _).mp
          branch
      obtain ⟨first, firstBranch, rfl⟩ := (Sql.branch_map_iff _ _ _ _ _ _).mp tailBranch
      simp only [List.allOk, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at ok
      have noError : found.output.isError = false := choice.not_error ok.1.1
      have reached := advance 0 (Nat.succ_pos _) index connection valid start output next others step found member noError
      have foundValid := runScriptStep_valid (profile := Profile.pinned) runContext clock index statement values rfl rfl
        valid found (by rw [step]; exact member)
      exact later (fun n => Inv (n + 1)) clock (index + 1) found.next first firstBranch
        (by simpa using returned) ok.2 foundValid reached
        (fun n inList index' connection' valid' holds output' next' others' step' found' member' noError' =>
          advance (n + 1) (Nat.succ_lt_succ inList) index' connection' valid' holds output' next' others' step' found'
            member' noError')

end Belay.Sqlite
