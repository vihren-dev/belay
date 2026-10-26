import Belay.Sqlite.ExecutionViewFrames
import Belay.Sqlite.MigrationPatternSuccess
import Belay.Sqlite.Model

set_option doc.verso true

/-! Programs under a constant clock (ADR 0017, S8). When the clock gives the same date at every statement
index, or there is no clock, the index at which a program starts changes nothing that the program does:
the same results are branches, the actual run is the same, and success is the same. A fact about one
start index then holds at every start index. The bridges from query translation to commutation
({lit}`MigrationQueryFrames`) need this, because an ordinary query moves the index. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

/-- For every program, every clock that gives one date at every index (or no clock), every pair of start
indices and every connection: a result is a branch from the first index exactly when it is a branch from
the second index. Plain words: a program that starts later, on the same connection, has the same set of
outcomes. Proof sketch: induction on the program. One step runs the same at both indices
({name}`runScriptStep_index`), so both sides continue with the same output, connection and choice, and
the induction hypothesis applies to the rest. -/
theorem Sql.branch_index_iff {α : Type} (program : Sql α) (clock : Option Clock)
    (constant : ∀ assignment ∈ clock, ∀ one other, assignment one = assignment other) :
    ∀ (first second : Nat) (connection : Connection) (result : SqlRun α),
      program.Branch clock first connection result ↔ program.Branch clock second connection result := by
  induction program with
  | pure value =>
    intro first second connection result
    rw [Sql.branch_pure_iff, Sql.branch_pure_iff]
  | exec statement values rest later =>
    intro first second connection result
    have same := runScriptStep_index runContext clock first second connection statement values
      (fun assignment member => constant assignment member _ _)
    cases step : runScriptStep runContext clock first connection statement values with
    | ended reason =>
      rw [Sql.branch_stopped_iff step, Sql.branch_stopped_iff (same.symm.trans step)]
    | continued output next others =>
      rw [Sql.branch_continued_iff step, Sql.branch_continued_iff (same.symm.trans step)]
      constructor
      · rintro ⟨selected, tail, choice, branch, rfl⟩
        exact ⟨selected, tail, choice, (later selected (first + 1) (second + 1) next tail).1 branch, rfl⟩
      · rintro ⟨selected, tail, choice, branch, rfl⟩
        exact ⟨selected, tail, choice, (later selected (first + 1) (second + 1) next tail).2 branch, rfl⟩

/-- For every program, every clock that gives one date at every index (or no clock), every pair of start
indices and every connection: the actual run from the first index is the actual run from the second
index. Plain words: the returned value, the outputs and the final connection do not depend on the start
index. Proof sketch: as for {name}`Sql.branch_index_iff`, with the actual step in place of a choice. -/
theorem Sql.runFrom_index {α : Type} (program : Sql α) (clock : Option Clock)
    (constant : ∀ assignment ∈ clock, ∀ one other, assignment one = assignment other) :
    ∀ (first second : Nat) (connection : Connection),
      program.runFrom clock first connection = program.runFrom clock second connection := by
  induction program with
  | pure value => intro first second connection; rfl
  | exec statement values rest later =>
    intro first second connection
    have same := runScriptStep_index runContext clock first second connection statement values
      (fun assignment member => constant assignment member _ _)
    simp only [Sql.runFrom, same]
    cases runScriptStep runContext clock second connection statement values with
    | ended reason => rfl
    | continued output next others => simp only [later output (first + 1) (second + 1) next]

/-- For every program, every clock that gives one date at every index (or no clock), every pair of start
indices and every connection: the program succeeds from the first index exactly when it succeeds from the
second index. Plain words: whether a program can fail or stop does not depend on the start index.
Proof sketch: success is a statement about all branches ({name}`Sql.succeedsFrom_iff_branches`), and the
branches do not depend on the index ({name}`Sql.branch_index_iff`). -/
theorem Sql.succeedsFrom_index {α : Type} (program : Sql α) (clock : Option Clock)
    (constant : ∀ assignment ∈ clock, ∀ one other, assignment one = assignment other)
    (first second : Nat) (connection : Connection) :
    program.SucceedsFrom clock first connection ↔ program.SucceedsFrom clock second connection := by
  simp only [Sql.succeedsFrom_iff_branches, Sql.branch_index_iff program clock constant first second connection]

end Belay.Sqlite
