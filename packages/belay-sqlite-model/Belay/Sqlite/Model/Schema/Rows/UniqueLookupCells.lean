import Belay.Sqlite.Model.Schema.Rows.LiteralData
import Belay.Sqlite.Model.Queries.Evaluation.IntegerCompareLaws

set_option doc.verso true

/-! The comparison of a stored cell with a value (ADR 0017, S4, outcome 6): when two stored cells of one
column are each equal to the same value in a comparison {lit}`c = v`, the two cells conflict as key cells
({name}`Belay.Sqlite.Model.LiteralData.keyCellsEqual`) under the collation of the comparison. This is the
step of a unique lookup that needs the affinity of the column. -/

namespace Belay.Sqlite.Model

namespace Resolved

/-- For every cell and affinity of INTEGER, REAL or NUMERIC: if the cell is in the form that a column of the affinity
stores ({name}`LiteralData.storedForm`), {name}`numericOperand` leaves it as it is. Proof sketch: only TEXT can change;
the store of a TEXT is its {name}`numericText`, or for REAL the read of that, which leaves a TEXT only when the
{name}`numericText` is the same TEXT. -/
theorem numericOperand_of_stored {affinity : Affinity} {cell : Value} (numeric : affinity ≠ .text ∧ affinity ≠ .blob)
    (stored : LiteralData.storedForm affinity cell = true) : numericOperand cell = cell := by
  simp only [LiteralData.storedForm, beq_iff_eq] at stored
  cases cell with
  | text bytes =>
    cases affinity with
    | text => exact absurd rfl numeric.1
    | blob => exact absurd rfl numeric.2
    | integer | numeric => exact stored
    | real =>
      simp only [Value.store, numericStore] at stored
      simp only [numericOperand]
      generalize numericText bytes = number at stored ⊢
      cases number <;> simp_all [realRead]
  | null | integer _ | real _ | blob _ => rfl

end Resolved
end Belay.Sqlite.Model
