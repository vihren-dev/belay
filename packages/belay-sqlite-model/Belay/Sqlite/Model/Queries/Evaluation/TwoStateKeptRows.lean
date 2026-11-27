import Belay.Sqlite.Model.Queries.Evaluation.CorrelatedSubqueryRun
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

/-- For any two input row lists, if every row kept by the condition in the first list
occurs in the second, each output of {name}`Resolved.initialTerm` occurs in the results
of {name}`Resolved.currentTerm` with the same columns and evaluation context.
Proof sketch: use the same input row as the witness for both projections. -/
theorem Resolved.project_selected_subset {before after : List (List Value)} {pos : Nat}
    {condition : Resolved.Expr} {columns : List Resolved.Expr} {names : List String} {ctx : Resolved.EvalContext}
    (survive : before.filter (conditionKeeps (some condition) ctx) ⊆ after) :
    (initialTerm pos condition columns names).results ctx before ⊆
      (currentTerm pos columns names).results ctx after := by
  intro output member
  obtain ⟨cells, scanned, kept, rfl⟩ := (initialTerm_mem_results ..).mp member
  exact (currentTerm_mem_results ..).mpr ⟨cells, survive (List.mem_filter.mpr ⟨scanned, kept⟩), rfl⟩

end Belay.Sqlite.Model
