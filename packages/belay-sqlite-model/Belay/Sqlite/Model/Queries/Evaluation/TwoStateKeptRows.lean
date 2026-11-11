import Belay.Sqlite.Model.Queries.Evaluation.TwoStateNotExistsExcept
import Belay.Sqlite.Model.Queries.Evaluation.PlainInsertRows

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every context, rows, condition and columns, a row is a result of the first term exactly when the output of a
source row that the condition keeps. In plain words: the term outputs the columns of the rows with a true condition.
Proof sketch: the rows of a simple query are the output rows of the rows that {lit}`WHERE` keeps
({name}`Resolved.Query.results_plain_unordered`). -/
theorem Resolved.initialTerm_mem_results (position : Nat) (condition : Resolved.Expr) (columns : List Resolved.Expr)
    (names : List String) (context : Resolved.EvalContext) (rows : List (List Value)) (output : List Value) :
    output ∈ (Resolved.initialTerm position condition columns names).results context rows ↔
      ∃ row ∈ rows, Resolved.truthy (condition.eval context row) = true ∧ output = columns.map (·.eval context row) := by
  rw [Resolved.Query.results_plain_unordered _ rfl rfl rfl rfl rfl rfl]
  simp only [List.mem_map, Resolved.mem_filtered, Resolved.Query.rowOutput, Resolved.Query.simple, Option.all_some]
  constructor
  · rintro ⟨row, ⟨member, kept⟩, rfl⟩
    exact ⟨row, member, kept, by simp [Function.comp_def]⟩
  · rintro ⟨row, member, kept, rfl⟩
    exact ⟨row, ⟨member, kept⟩, by simp [Function.comp_def]⟩

/-- For every context, rows and columns, a row is a result of the second term exactly when it is the output of a source
row. In plain words: the term outputs the columns of every row. Proof sketch: as
{name}`Resolved.initialTerm_mem_results`, without a condition. -/
theorem Resolved.currentTerm_mem_results (position : Nat) (columns : List Resolved.Expr) (names : List String)
    (context : Resolved.EvalContext) (rows : List (List Value)) (output : List Value) :
    output ∈ (Resolved.currentTerm position columns names).results context rows ↔
      ∃ row ∈ rows, output = columns.map (·.eval context row) := by
  rw [Resolved.Query.results_plain_unordered _ rfl rfl rfl rfl rfl rfl]
  simp only [List.mem_map, Resolved.mem_filtered, Resolved.Query.rowOutput, Resolved.Query.simple, Option.all_none,
    and_true]
  constructor
  · rintro ⟨row, member, rfl⟩
    exact ⟨row, member, by simp [Function.comp_def]⟩
  · rintro ⟨row, member, rfl⟩
    exact ⟨row, member, by simp [Function.comp_def]⟩

end Belay.Sqlite.Model
