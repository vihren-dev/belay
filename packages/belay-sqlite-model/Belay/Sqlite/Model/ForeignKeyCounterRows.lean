import Belay.Sqlite.Model.ForeignKeyCounterDelete
import Belay.Sqlite.Model.ForeignKeyCounterUpdate
import Belay.Sqlite.Model.ForeignKeyCounterInsert
import Belay.Sqlite.Model.ForeignKeyCounterNested
import Belay.Sqlite.Model.ForeignKeyCounterTriggers

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Actual row deletion preserves the foreign-key contract from a good input when the
nested runner, catalog comparisons and generated trigger/action conditions hold for the
matching frame. Proof sketch: discharge the deletion callbacks with trigger/action laws. -/
theorem deleteRow_nested_counter {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program} {nested : NestedRun}
    (keeps : nested.ForeignKeyKeeps profile catalog programs) (frame : RowFrame) (same : frame.programs = programs)
    (facts : catalog.ForeignKeyComparisons) (programSafe : ProgramsForeignKeySafe catalog programs)
    (actionSafe : ActionsForeignKeySafe catalog) (position : Nat) (record ignore fire : Bool)
    {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state) (rowid : Int) :
    ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
      (deleteRow catalog catalog.foreignKeyLinks nested frame position record ignore fire state rowid) :=
  deleteRow_counterBound frame position record ignore fire
    (fun time cells _ good => runPrograms_counterBound keeps frame same programSafe position time .delete cells good)
    (fun link member old _ good => runAction_foreignKeyInvariant keeps frame same actionSafe link
      (List.mem_filter.mp (List.mem_reverse.mp member)).1 _ (.inl rfl) position old none good)
    (fun link inside key child parent located childAt parentAt =>
      facts.scans link inside position key child parent located childAt parentAt) good rowid

/-- Under the nested deletion conditions, actual REPLACE deletion preserves the
foreign-key contract. Proof sketch: apply deletion with the REPLACE frame and restore
statement-count metadata, which changes neither rows nor the immediate counter. -/
theorem replaceDelete_nested_counter {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program} {nested : NestedRun}
    (keeps : nested.ForeignKeyKeeps profile catalog programs) (frame : RowFrame) (same : frame.programs = programs)
    (facts : catalog.ForeignKeyComparisons) (programSafe : ProgramsForeignKeySafe catalog programs)
    (actionSafe : ActionsForeignKeySafe catalog) (position : Nat)
    {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state) (row : Row) :
    ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
      (replaceDelete catalog catalog.foreignKeyLinks nested frame position state row) :=
  KeyResult.mapState_foreignKeyInvariant (change := fun deleted : KeyState => {deleted with own := state.own}) (fun _ => rfl) (fun _ => rfl)
    (deleteRow_nested_counter keeps {frame with algorithm := some .replace} same facts programSafe actionSafe
      position false false frame.recursive good row.rowid)

/-- Actual row UPDATE preserves the foreign-key contract from a good input when the
nested runner, catalog comparisons, generated trigger/actions, safe change and BEFORE
target frame conditions hold. Proof sketch: use the target frame to retain the captured
row and discharge actual UPDATE's program/action callbacks. -/
theorem updateRow_nested_counter {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program} {nested : NestedRun}
    (keeps : nested.ForeignKeyKeeps profile catalog programs) (frame : RowFrame) (same : frame.programs = programs)
    (facts : catalog.ForeignKeyComparisons) (programSafe : ProgramsForeignKeySafe catalog programs)
    (actionSafe : ActionsForeignKeySafe catalog) (before : nested.BeforeUpdateFrame profile catalog programs)
    (position : Nat) (change : Row → Row) (assigned changed : List Nat) (record : Bool)
    (safe : ForeignKeyUpdateConditions catalog position change changed)
    {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state) (rowid : Int) :
    ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
      (updateRow catalog catalog.foreignKeyLinks nested frame position change assigned changed record state rowid) :=
  updateRow_counterBound frame position change assigned changed record facts safe.cells safe.scans
    (fun time cells _ good => runPrograms_counterBound keeps frame same programSafe position time _ cells good)
    (fun link member old new _ good => runAction_foreignKeyInvariant keeps frame same actionSafe link
      (List.mem_filter.mp (List.mem_reverse.mp member)).1 _ (.inr rfl) position old (some new) good)
    good rowid (fun old found reached ended ran notEnded => by
      rw [before frame position assigned _ state reached ended same good.1.1 ran notEnded]
      exact List.mem_of_find?_eq_some found)

/-- Actual insertion preserves the foreign-key contract from a good input under the
matching frame's nested-run, catalog-comparison and generated trigger/action conditions.
Proof sketch: discharge insertion's callbacks with program and REPLACE deletion laws. -/
theorem insertRow_nested_counter {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program} {nested : NestedRun}
    (keeps : nested.ForeignKeyKeeps profile catalog programs) (frame : RowFrame) (same : frame.programs = programs)
    (facts : catalog.ForeignKeyComparisons) (programSafe : ProgramsForeignKeySafe catalog programs)
    (actionSafe : ActionsForeignKeySafe catalog) (position : Nat) (policy : Resolved.ConflictPolicy)
    (clauses : List Resolved.ConflictClause) (multiWrite record : Bool)
    {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state) (values : List Value) :
    ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
      (insertRow catalog catalog.foreignKeyLinks nested frame position policy clauses multiWrite record state values) :=
  insertRow_counterBound frame position policy clauses multiWrite record facts
    (fun time cells _ good => runPrograms_counterBound keeps frame same programSafe position time .insert cells good)
    (fun _ row good => replaceDelete_nested_counter keeps frame same facts programSafe actionSafe position good row)
    good values

/-- For every fuel, the actual row engine preserves the foreign-key success/stop
contract for matching frames and safe work when catalog comparisons, generated trigger
and action conditions hold and every credited lower-fuel runner has the BEFORE target
frame. Zero fuel is undescribed and imposes nothing. This permits pending violations
inside execution and does not assume the final row-reference atom.
Proof sketch: induct over fuel; the credited induction hypothesis discharges nested
triggers/actions, then fold the actual DELETE, UPDATE or INSERT rows. -/
theorem runRows_foreignKeyKeeps (profile : Profile) (catalog : Catalog) (programs : List Resolved.Program)
    (facts : catalog.ForeignKeyComparisons) (programSafe : ProgramsForeignKeySafe catalog programs)
    (actionSafe : ActionsForeignKeySafe catalog)
    (before : ∀ fuel, (NestedRun.credited (runRows catalog catalog.foreignKeyLinks fuel)).BeforeUpdateFrame profile catalog programs) :
    ∀ fuel, NestedRun.ForeignKeyKeeps profile catalog programs (runRows catalog catalog.foreignKeyLinks fuel)
  | 0 => by intro _ _ _ _ _ _; trivial
  | fuel + 1 => by
    have nested := NestedRun.credited_foreignKeyKeeps (runRows_foreignKeyKeeps profile catalog programs facts programSafe actionSafe before fuel)
    intro frame work state same safe good
    cases work with
    | delete position rowids record ignore fire =>
      exact ResultHolds.foldlM (fun _ rowid good =>
        deleteRow_nested_counter nested frame same facts programSafe actionSafe position record ignore fire good rowid) rowids state good
    | update position change assigned changed rowids record =>
      exact ResultHolds.foldlM (fun _ rowid good =>
        updateRow_nested_counter nested frame same facts programSafe actionSafe (before fuel)
          position change assigned changed record safe good rowid) rowids state good
    | insert position rows policy clauses multiWrite record =>
      exact ResultHolds.foldlM (fun _ values good =>
        insertRow_nested_counter nested frame same facts programSafe actionSafe position policy clauses multiWrite record good values) rows state good

end Belay.Sqlite.Model
