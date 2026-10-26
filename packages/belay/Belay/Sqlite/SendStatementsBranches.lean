import Belay.Sqlite.ExecutionBranchLaws
import Belay.Sqlite.ProgramLaws

set_option doc.verso true

/-! The branches of mapped programs and of sent statements (ADR 0017, S6). Sending statements
does not choose later statements from earlier outputs, so every raw or concrete branch of a
script reaches the connection of its actual run and has as many outputs as that run. -/

namespace Belay.Sqlite
open Model

/-- For every function, program and starting inputs, a result is a branch of the mapped
program exactly when it is a branch of the program with the function applied to its value.
Outputs and the final connection stay as they were. Proof sketch: induction on the program;
each step of the mapped program is the step of the program, and only the pure leaf changes. -/
theorem Sql.branch_map_iff {α β : Type} (function : α → β) (program : Sql α) :
    ∀ clock index connection (result : SqlRun β),
      (program.map function).Branch clock index connection result ↔
        ∃ first, program.Branch clock index connection first ∧
          result = { first with value := first.value.map function } := by
  induction program with
  | pure value =>
    intro clock index connection result
    change (Sql.pure (function value)).Branch clock index connection result ↔ _
    rw [Sql.branch_pure_iff]
    constructor
    · rintro rfl
      exact ⟨{ outputs := [], connection, value := some value }, (Sql.branch_pure_iff value _ _ _ _).mpr rfl, rfl⟩
    · rintro ⟨first, branch, rfl⟩
      rw [(Sql.branch_pure_iff value _ _ _ first).mp branch]
      rfl
  | exec statement values rest later =>
    intro clock index connection result
    change (Sql.exec statement values fun output => (rest output).map function).Branch clock index connection
      result ↔ _
    cases step : runScriptStep runContext clock index connection statement values with
    | ended reason =>
      rw [Sql.branch_stopped_iff (rest := fun output => (rest output).map function) step]
      constructor
      · rintro rfl
        exact ⟨_, (Sql.branch_stopped_iff (rest := rest) step _).mpr rfl, rfl⟩
      · rintro ⟨first, branch, rfl⟩
        rw [(Sql.branch_stopped_iff (rest := rest) step first).mp branch]
        rfl
    | continued actual next others =>
      rw [Sql.branch_continued_executions_iff (rest := fun output => (rest output).map function) step]
      constructor
      · rintro ⟨found, member, selected, tail, choice, branch, rfl⟩
        obtain ⟨first, firstBranch, rfl⟩ := (later selected _ _ _ tail).mp branch
        exact ⟨{ first with outputs := selected :: first.outputs },
          (Sql.branch_continued_executions_iff (rest := rest) step _).mpr
            ⟨found, member, selected, first, choice, firstBranch, rfl⟩, rfl⟩
      · rintro ⟨first, branch, rfl⟩
        obtain ⟨found, member, selected, tail, choice, tailBranch, rfl⟩ :=
          (Sql.branch_continued_executions_iff (rest := rest) step first).mp branch
        exact ⟨found, member, selected, { tail with value := tail.value.map function }, choice,
          (later selected _ _ _ _).mpr ⟨tail, tailBranch, rfl⟩, rfl⟩

/-- For every list of statements with inputs, none of which resolves to an INSERT from a query without
rules ({name}`ScriptConditionsWith` for {lit}`fromQuery = false`), and every branch of the sent program, the
branch reaches the connection of the model's script run and has as many outputs as that run. This holds
for every raw and every concrete choice of a {lit}`oneOf` output, because a step's next connection does not
depend on the chosen output. With an INSERT from a query, another execution of the statement can reach another
connection. Proof sketch: induction on the statements. A stopping step gives the
same one-output result in both. After a continuing step, which has one execution
({name}`ScriptConditionsWith.single_step`), {name}`Sql.branch_map_iff` reduces the branch to a branch of the
remaining statements. -/
theorem sendStatements_branch_shape (statements : List (Syntax.Statement × List Value)) :
    ∀ clock index connection (result : SqlRun (List Output)),
      ScriptConditionsWith (fun resolved _ => resolved.fromQuery = false) runContext clock index connection statements →
      (sendStatements statements).Branch clock index connection result →
        result.connection = (runScriptFrom runContext clock index connection statements).connection ∧
        result.outputs.length = (runScriptFrom runContext clock index connection statements).outputs.length := by
  induction statements with
  | nil =>
    intro clock index connection result _ branch
    obtain rfl := (Sql.branch_pure_iff _ _ _ _ _).mp branch
    exact ⟨rfl, rfl⟩
  | cons head rest later =>
    rcases head with ⟨statement, values⟩
    intro clock index connection result single branch
    cases step : runScriptStep runContext clock index connection statement values with
    | ended reason =>
      obtain rfl := (Sql.branch_stopped_iff (rest := fun output => (sendStatements rest).map (output :: ·)) step _).mp
        branch
      simp [runScriptFrom, step]
    | continued output next others =>
      obtain ⟨noOthers, restSingle⟩ := ScriptConditionsWith.single_step single step
      obtain ⟨selected, tail, _, tailBranch, rfl⟩ :=
        (Sql.branch_continued_iff (rest := fun output => (sendStatements rest).map (output :: ·)) step noOthers _).mp branch
      obtain ⟨first, firstBranch, rfl⟩ := (Sql.branch_map_iff _ _ _ _ _ _).mp tailBranch
      obtain ⟨connectionEq, lengthEq⟩ := later _ _ _ first restSingle firstBranch
      simp [runScriptFrom, step, connectionEq, lengthEq]

end Belay.Sqlite
