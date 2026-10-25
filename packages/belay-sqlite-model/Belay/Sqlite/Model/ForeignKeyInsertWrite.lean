import Belay.Sqlite.Model.ForeignKeyEngineFacts
import Belay.Sqlite.Model.ForeignKeyInsertBound

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For a good input, an admitted row accepted by the actual uniqueness/row checks
and new-key checks gives a good appended state. The checked state must retain the input
rows, and catalog comparisons must hold for future stored values.
Proof sketch: combine the existing admitted-write law with the append counter bound. -/
theorem insertWrite_counterBound {profile : Profile} {catalog : Catalog} {state checked : KeyState} {target : Nat}
    {entry : CatalogTable} (entryFound : catalog.tableAt target = some entry) {current next : Table}
    {proposed : Row} {written : Option Row} (good : KeyState.ForeignKeyInvariant profile catalog state) (facts : catalog.ForeignKeyComparisons)
    (same : checked.rows = state.rows)
    (found : (checked.database catalog).table target = some current)
    (admitted : LiteralData.rowAdmitted current.shape proposed = true)
    (passed : LiteralData.checkedRow (catalog.uniqueKeys target entry)
      { shape := current.shape, rows := current.rows ++ [proposed] } proposed = .ok (next, written))
    (scan : Bool) (newResult : newSteps catalog state target proposed (childLinks catalog.foreignKeyLinks target)
      (parentLinks catalog.foreignKeyLinks target) scan none [] = .ok checked) :
    KeyState.ForeignKeyInvariant profile catalog (checked.changeRows target fun _ => next.rows) := by
  have ready : checked.Holds (Database.ForeignKeyReady profile) catalog := KeyState.holds_of_rows same good.1
  refine ⟨insertWrite_holds ((admittedWriteLaws profile).and keysUniqueFacts.laws) entryFound ready found admitted passed, ?_⟩
  have currentEntry : current.shape = entry := by
    have first := KeyState.table_shape found
    rw [entryFound, Option.some.injEq] at first
    exact first.symm
  have atState : (state.database catalog).table target = some current := by
    simpa only [KeyState.database, same] using found
  obtain ⟨stored, constraints⟩ := LiteralData.checkedRow_passed passed
  subst next
  rw [← currentEntry] at constraints
  have bound := newSteps_append_parent_counterBound good.2 atState
    (KeyState.table_aligned good.1.1.rowsShaped atState) good.1.1.rowsStored proposed
    ((LiteralData.rowAdmitted_iff _ _).mp admitted).2.2.1
    (keysUniqueFacts.constraints _ _ _ constraints) (passed_rowidsDistinct constraints)
    (fun link inside key child located childAt => facts.scans link inside target key child.shape current.shape located
      (KeyState.table_shape childAt) (KeyState.table_shape atState))
    (fun link inside pairs located => facts.unique link inside target pairs current.shape located (KeyState.table_shape atState))
    (fun link inside key located => by
      have childAt : link.child = target := by
        simpa only [beq_iff_eq] using (List.mem_filter.mp (List.mem_reverse.mp inside)).2
      exact facts.self link (List.mem_filter.mp (List.mem_reverse.mp inside)).1 key current.shape
        (by simpa only [childAt] using located) (by simpa only [childAt] using KeyState.table_shape atState)) scan
  rw [newResult] at bound
  change (checked.changeRows target (· ++ [proposed])).CounterBound catalog at bound
  simpa only [KeyState.CounterBound, KeyState.database, KeyState.changeRows, KeyState.table_rows found] using bound

end Belay.Sqlite.Model
