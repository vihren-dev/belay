import Belay.Sqlite.Model.RowEngineKeyState
import Belay.Sqlite.Model.DatabaseFacts

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For any result satisfying two success/stop contracts, it satisfies both contracts
on its actual branch. Proof sketch: inspect success or error and pair the given facts. -/
theorem ResultHolds.and {α} {a b : α → Prop} {sa sb : KeyStop → Prop} {result : Except KeyStop α}
    (first : ResultHolds a sa result) (second : ResultHolds b sb result) :
    ResultHolds (fun value => a value ∧ b value) (fun stop => sa stop ∧ sb stop) result := by
  cases result <;> exact ⟨first, second⟩

/-- For any result satisfying a success/stop contract, each success also records that
it is the actual result; the stop contract is unchanged. Proof sketch: inspect the result. -/
theorem ResultHolds.with_eq {α} {good : α → Prop} {stopGood : KeyStop → Prop}
    {result : Except KeyStop α} (holds : ResultHolds good stopGood result) :
    ResultHolds (fun value => good value ∧ result = .ok value) stopGood result := by
  cases result <;> first | exact holds | exact ⟨holds, rfl⟩

/-- For any list, if each member's step preserves the success fact or establishes the
stop fact, folding from a good input has that contract. An empty list keeps the input fact.
Proof sketch: induct over the list and compose the actual monadic steps. -/
theorem ResultHolds.foldlM_mem {α β} {good : β → Prop} {stopGood : KeyStop → Prop}
    {step : β → α → Except KeyStop β} (list : List α)
    (steps : ∀ value element, element ∈ list → good value → ResultHolds good stopGood (step value element))
    (start : β) (holds : good start) : ResultHolds good stopGood (list.foldlM step start) := by
  induction list generalizing start with
  | nil => exact holds
  | cons first rest induction =>
    rw [List.foldlM_cons]
    apply ResultHolds.bind (steps start first (by simp) holds)
    intro value reached
    exact induction (fun state item member good => steps state item (by simp [member]) good) value reached

/-- For every row-shaped key state, a successful table lookup is within the row-store
length. Proof sketch: the catalog position is in bounds and row shape equates both lengths. -/
theorem KeyState.table_aligned {catalog : Catalog} {state : KeyState} {position : Nat} {table : Table}
    (shaped : (state.database catalog).RowsShaped) (found : (state.database catalog).table position = some table) :
    position < state.rows.length := by
  have atShape := KeyState.table_shape found
  unfold Catalog.tableAt at atShape
  cases atObject : catalog[position]? with
  | none => simp [atObject] at atShape
  | some object =>
    have below := List.getElem?_eq_some_iff.mp atObject |>.1
    have aligned : state.rows.length = catalog.length := shaped.1
    omega

/-- For any row found by rowid in a key state, a table exists at that position, contains
the row and gives it the searched rowid. Proof sketch: unpack the successful list lookup. -/
theorem KeyState.foundRow_table {catalog : Catalog} {state : KeyState} {position : Nat} {rowid : Int} {row : Row}
    (found : ((state.database catalog).rowsAt position).find? (·.rowid == rowid) = some row) :
    ∃ table, (state.database catalog).table position = some table ∧ row ∈ table.rows ∧ row.rowid = rowid := by
  have member := List.mem_of_find?_eq_some found
  have same : row.rowid = rowid := beq_iff_eq.mp (List.find?_some (p := fun row : Row => row.rowid == rowid) found)
  cases atTable : (state.database catalog).table position with
  | none => simp [Database.rowsAt, atTable] at member
  | some table =>
    refine ⟨table, rfl, ?_, same⟩
    simpa [Database.rowsAt, atTable] using member

end Belay.Sqlite.Model
