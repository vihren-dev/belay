import Belay.Sqlite.ExecutionSpecifications
import Belay.Sqlite.ExecutionStep
import Belay.Sqlite.Model.SelectStepKeeps
import Belay.Sqlite.ProgramQueries

set_option doc.verso true

/-!
What a program that selects one value and then uses it checks in a fresh run (ADR 0017, S6). A
universal claim about such a program needs three facts: the check of the single-value query is a
statement about its one step ({lit}`check_single_of_statement`), the value that the query returns
is one of the values that the output offers ({lit}`selectedValues`), and a SELECT leaves the
connection as it was ({name}`Belay.Sqlite.Model.runScriptStep_select_connection`).
-/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every script of one statement and every post and context: a program that reads the single
value of the script checks the post exactly when the step of the statement continues, and the post
holds for every selected output, with the single value of its rows, at the context after the step.
Proof sketch: {name}`check_single` and {name}`check_query`; unpack the one statement of the script. -/
theorem check_single_of_statement {statement : Syntax.Statement} {values : List Value}
    (script : Script) (one : script.statements.length = 1) (isStatement : script.statements = [(statement, values)])
    (post : Option Value → ExecutionContext → Prop) (state : ExecutionContext) :
    (single script one).check post state ↔
      match runScriptStep runContext state.clock state.index state.connection statement values with
      | .ended _ => False
      | .continued actual connection =>
        ∀ selected, OutputChoice actual selected →
          post (singleValue (queryResult selected)) (state.next selected connection) := by
  rw [check_single, check_query]
  obtain ⟨statements⟩ := script
  simp only at isStatement
  subst isStatement
  rfl

/-- The single values that the rows of an output offer: the value of the output itself, and the
value of each alternative of a choice. -/
def selectedValues (output : Output) : List Value :=
  (singleValue (queryResult output) :: match output with
    | .oneOf alternatives => alternatives.map fun rows => singleValue (.ok rows)
    | .done _ | .rows _ | .error _ | .unmodeled _ => []).filterMap id

/-- For every output, every selected output of it and every value: if the selected output has the
value as its single value, then {name}`selectedValues` of the output contains the value. Proof
sketch: a selected output is the output or one alternative of a choice. -/
theorem mem_selectedValues {output selected : Output} {next : Value} (choice : OutputChoice output selected)
    (single : singleValue (queryResult selected) = some next) : next ∈ selectedValues output := by
  unfold selectedValues
  rcases choice with rfl | choice
  · simp [single]
  · cases output <;> simp at choice
    rename_i alternatives
    obtain ⟨rows, mem, rfl⟩ := choice
    simp only [List.mem_filterMap, List.mem_cons, List.mem_map]
    exact ⟨some next, Or.inr ⟨rows, mem, by simpa [queryResult] using single⟩, rfl⟩

/-- For every output, every selected output of it and every value: if the selected output has a
single value, the output is not an error. Proof sketch: an error has no single value, and a choice
whose alternative has one is not an error. -/
theorem not_error_of_single {output selected : Output} {next : Value} (choice : OutputChoice output selected)
    (single : singleValue (queryResult selected) = some next) : output.isError = false := by
  rcases choice with rfl | choice
  · cases selected <;> simp_all [queryResult, singleValue, Output.isError]
  · cases output <;> simp at choice <;> simp [Output.isError]

/-- For every database and every two counters: the resolution state of the idle connection does not
depend on the counters. -/
theorem connection_resolveState (raw : Database.Raw) (first second : Counters) :
    (raw.connection first).resolveState = (raw.connection second).resolveState := rfl

end Belay.Sqlite
