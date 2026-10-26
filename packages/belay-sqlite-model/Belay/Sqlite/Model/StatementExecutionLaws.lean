import Belay.Sqlite.Model.StatementExecution

set_option doc.verso true

/-! Laws of the executions of a statement (ADR 0019, D4, amended 2026-10-25). They are a module apart
from {lit}`StatementExecution.lean`, so that the definitions need no proof. -/

namespace Belay.Sqlite.Model

/-- For every index, values, connection, resolved statement, resolution state, clock value and run
without alternatives, the further executions ({name}`StatementExecution.ofAlternatives`) are none.
Proof sketch: the map over no alternatives is the empty list. -/
theorem StatementExecution.ofAlternatives_of_single (index : Nat) (parameters : List Value) (connection : Connection)
    (resolved : Resolved.Statement) (after : ResolveState) (value : Int) {run : StatementRun}
    (single : run.alternatives = []) :
    StatementExecution.ofAlternatives index parameters connection resolved after value run = .ok [] := by
  simp only [StatementExecution.ofAlternatives, single, List.mapM_nil]
  rfl

/-- For every execution, each execution that it stands for ({name}`StatementExecution.expand`) has
its next connection. Proof sketch: split on the output; a result keeps the connection. -/
theorem StatementExecution.expand_next (execution : StatementExecution) :
    ∀ other ∈ execution.expand, other.next = execution.next := by
  unfold StatementExecution.expand
  split <;> simp_all

/-- For every execution with the output {name}`Output.oneOf` of the results and every list of
rows: some execution that it stands for ({name}`StatementExecution.expand`) has the output
{name}`Output.rows` of the rows exactly when the rows are one of the results. It requires nothing
of rows outside the list. Proof sketch: the executions are the results, one for each. -/
theorem StatementExecution.mem_expand_rows {execution : StatementExecution} {results : List (List (List Value))}
    (output : execution.output = .oneOf results) (rows : List (List Value)) :
    (∃ other ∈ execution.expand, other.output = .rows rows) ↔ rows ∈ results := by
  unfold StatementExecution.expand
  simp only [output, List.mem_map]
  constructor
  · rintro ⟨_, ⟨found, member, rfl⟩, same⟩
    cases same
    exact member
  · intro member
    exact ⟨_, ⟨rows, member, rfl⟩, rfl⟩

end Belay.Sqlite.Model
