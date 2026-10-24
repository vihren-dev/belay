import Belay.Sqlite.Model.ForeignKeyEngineFacts
import Belay.Sqlite.Model.ForeignKeyCountDelete

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For any good input, actual row deletion preserves the foreign-key invariant on
success and its stop contract, provided applicable trigger programs and parent actions do
so and catalog-selected child scans agree with lookups. These callbacks describe the
nested runner, not the final deletion result. Missing targets keep the input invariant.
Proof sketch: bound the physical removal, then fold actual actions and trigger programs. -/
theorem deleteRow_counterBound {profile : Profile} {catalog : Catalog} {nested : NestedRun}
    (frame : RowFrame) (position : Nat) (record ignore fire : Bool)
    (programs : ∀ time cells state, KeyState.ForeignKeyInvariant profile catalog state →
      ResultHolds (fun pair : KeyState × Bool => KeyState.ForeignKeyInvariant profile catalog pair.1) (KeyStop.ForeignKeyInvariant profile catalog)
        (runPrograms catalog nested frame position time .delete cells state))
    (actions : ∀ link ∈ parentLinks catalog.foreignKeyLinks position, ∀ old state,
      KeyState.ForeignKeyInvariant profile catalog state → ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
        (runAction catalog (nested frame.action) link link.key.onDelete position old none state))
    (consistent : ∀ link ∈ catalog.foreignKeyLinks, ∀ key child parent,
      link.parent = .located position key → catalog.tableAt link.child = some child →
      catalog.tableAt position = some parent → link.LookupScanConsistent child parent key)
    {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state) (rowid : Int) :
    ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
      (deleteRow catalog catalog.foreignKeyLinks nested frame position record ignore fire state rowid) := by
  unfold deleteRow
  split
  · dsimp only
    split <;> refine ResultHolds.bind (good := fun pair : KeyState × Bool => KeyState.ForeignKeyInvariant profile catalog pair.1) ?_
      fun pair good => ?_
    all_goals first | exact programs _ _ _ good | exact good | skip
    all_goals
      obtain ⟨reached, ended⟩ := pair
      dsimp only
      split
      · exact good
      · split
        · rename_i old foundOld
          obtain ⟨table, found, member, rowidAt⟩ := KeyState.foundRow_table foundOld
          have bounded := oldSteps_remove_parent_counterBound good.2 found
            (KeyState.table_aligned good.1.1.rowsShaped found) (good.1.1.rowidsDistinct position table found)
            good.1.1.rowsStored old member
            (fun link inside key child located childAt =>
              consistent link inside key child.shape table.shape located
                (KeyState.table_shape childAt) (KeyState.table_shape found)) ignore
          have same := oldSteps_rows catalog reached position old
            (childLinks catalog.foreignKeyLinks position) (parentLinks catalog.foreignKeyLinks position) ignore
          have phase : ResultHolds (fun checked : KeyState =>
              KeyState.ForeignKeyInvariant profile catalog { checked.changeRows position (fun rows => rows.filter (·.rowid != rowid)) with
                written := if record then checked.written ++ [old] else checked.written, own := checked.own + 1 })
              (KeyStop.ForeignKeyInvariant profile catalog)
              (oldSteps catalog reached position old (childLinks catalog.foreignKeyLinks position)
                (parentLinks catalog.foreignKeyLinks position) ignore) := by
            cases result : oldSteps catalog reached position old (childLinks catalog.foreignKeyLinks position)
                (parentLinks catalog.foreignKeyLinks position) ignore with
            | error stop =>
              rw [result] at same
              subst stop
              trivial
            | ok checked =>
              rw [result] at same bounded
              have retained := KeyState.holds_of_rows same good.1
              have removed := KeyState.holds_changeRows_sublist
                ((admittedWriteLaws profile).and keysUniqueFacts.laws) retained
                (position := position) (change := fun rows => rows.filter (·.rowid != rowid))
                (fun _ => List.filter_sublist)
              refine ⟨removed, ?_⟩
              change (checked.changeRows position (fun rows => rows.filter (·.rowid != old.rowid))).CounterBound catalog at bounded
              simpa only [KeyState.CounterBound, KeyState.database, KeyState.changeRows, rowidAt] using bounded
          refine ResultHolds.bind phase fun checked checkedGood => ?_
          refine ResultHolds.bind (ResultHolds.foldlM_mem _ (fun acted link member good => ?_) _ checkedGood)
            fun acted good => ?_
          · exact actions link member old acted good
          · first | exact good | exact ResultHolds.bind (programs _ _ _ good) fun _ reached => reached
        · exact good
  · exact good

end Belay.Sqlite.Model
