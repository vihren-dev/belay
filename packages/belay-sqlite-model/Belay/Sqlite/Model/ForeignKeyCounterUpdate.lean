import Belay.Sqlite.Model.ForeignKeyUpdateChecks

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For a good input, the actual row UPDATE preserves the foreign-key invariant on
success and the stop contract when comparison, effect coverage and stale-scan conditions
hold, nested programs/actions preserve the invariant, and a continuing BEFORE trigger
retains the captured old row. Missing rows keep the input fact. The target-retention
premise concerns BEFORE execution only; it does not assume final row-reference truth.
Proof sketch: follow the actual checks, retain their result equalities, apply the covered
replacement bound, and compose actual actions and AFTER programs. -/
theorem updateRow_counterBound {profile : Profile} {catalog : Catalog} {nested : NestedRun}
    (frame : RowFrame) (position : Nat) (change : Row → Row) (assigned changed : List Nat) (record : Bool)
    (facts : catalog.ForeignKeyComparisons)
    (covers : ∀ shape, catalog.tableAt position = some shape → RowChange.Covers shape changed change)
    (noStaleScan : ∀ name shape, catalog[position]? = some {name, entry := .table shape} →
      (updateLevel catalog.foreignKeyLinks position name shape changed ≤ 1 ∧
        (shape.rowidAlias.any changed.contains || (shape.withoutRowid && shape.primaryKey.any changed.contains)) = false) →
      ∀ link ∈ (parentLinks catalog.foreignKeyLinks position).filter (·.key.parentChanged shape changed), link.child ≠ position)
    (programs : ∀ time cells state, KeyState.ForeignKeyInvariant profile catalog state →
      ResultHolds (fun pair : KeyState × Bool => KeyState.ForeignKeyInvariant profile catalog pair.1) (KeyStop.ForeignKeyInvariant profile catalog)
        (runPrograms catalog nested frame position time (.update (some assigned)) cells state))
    (actions : ∀ link ∈ parentLinks catalog.foreignKeyLinks position, ∀ old new state,
      KeyState.ForeignKeyInvariant profile catalog state → ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
        (runAction catalog (nested frame.action) link link.key.onUpdate position old (some new) state))
    {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state) (rowid : Int)
    (retainsOld : ∀ old, ((state.database catalog).rowsAt position).find? (·.rowid == rowid) = some old →
      ∀ reached ended, runPrograms catalog nested frame position .before (.update (some assigned))
        ((change old).values ++ old.values) state = .ok (reached, ended) → ended = false →
        old ∈ (reached.database catalog).rowsAt position) :
    ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
      (updateRow catalog catalog.foreignKeyLinks nested frame position change assigned changed record state rowid) := by
  unfold updateRow
  split
  · rename_i old name shape foundOld atObject
    have oldRowid : old.rowid = rowid := beq_iff_eq.mp (List.find?_some (p := fun row : Row => row.rowid == rowid) foundOld)
    obtain ⟨table, present, member, _⟩ := KeyState.foundRow_table foundOld
    have atShape : catalog.tableAt position = some shape := by simp only [Catalog.tableAt, atObject]
    extract_lets new event level children parents moved stale afterOldSteps afterChecks afterAlias
    have stored : ∀ reached before checked : KeyState,
        KeyState.ForeignKeyInvariant profile catalog reached → old ∈ (reached.database catalog).rowsAt position →
        checkedUpdate catalog reached position old new = .ok () → before.rows = reached.rows →
        (if level != 0 then oldSteps catalog reached position old children parents false else pure reached) = .ok before →
        (if level != 0 then newSteps catalog (before.changeRows position (fun rows => rows.filter (·.rowid != rowid)))
          position new children parents true stale changed else pure (before.changeRows position (fun rows => rows.filter (·.rowid != rowid)))) = .ok checked →
        KeyState.ForeignKeyInvariant profile catalog ({ checked with rows := before.rows, written := if record then checked.written ++ [new] else checked.written, own := checked.own + 1 }.changeRows position (fun rows => rows.map fun (row : Row) => if row.rowid == rowid then new else row)) := by
      intro reached before checked reachedGood stillThere passed same oldResult newResult
      let current : Table := {shape, rows := reached.rows.getD position []}
      have currentFound : (reached.database catalog).table position = some current := by
        simp only [Database.table, KeyState.database, atShape, Option.map_some, current]
      have currentMember : old ∈ current.rows := by
        simpa only [Database.rowsAt, currentFound, Option.map_some, Option.getD_some] using stillThere
      have ready := updateWrite_holds ((admittedWriteLaws profile).and keysUniqueFacts.laws)
        (other := { checked with rows := before.rows, written := if record then checked.written ++ [new] else checked.written, own := checked.own + 1 }) reachedGood.1 passed same oldRowid rfl
      refine ⟨ready, ?_⟩
      have bounded := updateChecks_covered_bound reachedGood facts atObject currentFound change changed (covers shape atShape)
        old currentMember passed (noStaleScan name shape atObject) oldResult (by simpa only [oldRowid] using newResult)
      have tableRows := KeyState.table_rows currentFound
      simpa only [KeyState.CounterBound, KeyState.database, KeyState.changeRows, LiteralData.replaceRow,
        Database.setRows, same, tableRows, oldRowid, new] using bounded
    have afterOldStepsOk : ∀ reached before : KeyState,
        KeyState.ForeignKeyInvariant profile catalog reached → old ∈ (reached.database catalog).rowsAt position →
        checkedUpdate catalog reached position old new = .ok () → before.rows = reached.rows →
        (if level != 0 then oldSteps catalog reached position old children parents false else pure reached) = .ok before →
        ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog) (afterOldSteps before) := by
      intro reached before reachedGood stillThere passed same oldResult
      dsimp only [afterOldSteps]
      have afterNew : ∀ checked,
          (if level != 0 then newSteps catalog (before.changeRows position (fun rows => rows.filter (·.rowid != rowid)))
            position new children parents true stale changed else pure (before.changeRows position (fun rows => rows.filter (·.rowid != rowid)))) = .ok checked →
          ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
            (do
              let state ← parents.foldlM (fun state link => runAction catalog (nested frame.action) link link.key.onUpdate position old (some new) state)
                ({ checked with rows := before.rows, written := if record then checked.written ++ [new] else checked.written, own := checked.own + 1 }.changeRows position (fun rows => rows.map fun (row : Row) => if row.rowid == rowid then new else row))
              return (← runPrograms catalog nested frame position .after event (new.values ++ old.values) state).1) := by
        intro checked newResult
        refine ResultHolds.bind (ResultHolds.foldlM_mem parents (fun state link inside good =>
          actions link (List.mem_filter.mp inside).1 old new state good) _ (stored reached before checked reachedGood stillThere passed same oldResult newResult))
          fun state good => ?_
        exact ResultHolds.bind (programs _ _ _ good) fun _ good => good
      split
      · rename_i active
        have rows := (newSteps_rows catalog (before.changeRows position (fun rows => rows.filter (·.rowid != rowid)))
          position new children parents true stale changed).with_eq
        refine ResultHolds.bind (rows.imp (fun _ pair => pair.2) (fun stop undescribed => undescribed ▸ ⟨trivial, trivial⟩))
          fun checked newResult => afterNew checked ?_
        simpa only [active, ite_true] using newResult
      · rename_i inactive
        exact afterNew _ (by simp only [inactive]; rfl)
    have afterChecksOk : ∀ resumed : Unit, ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog) (afterChecks resumed) := by
      intro _
      dsimp only [afterChecks]
      refine ResultHolds.bind ((programs .before _ _ good).with_eq) fun pair pairGood => ?_
      obtain ⟨reached, ended⟩ := pair
      obtain ⟨reachedGood, ran⟩ := pairGood
      dsimp only
      split
      · exact reachedGood
      · rename_i notEnded
        have stillThere := retainsOld old foundOld reached ended ran (by simpa only [Bool.not_eq_true] using notEnded)
        split
        · rename_i stop failed
          split
          · unfold checkedUpdate at failed
            repeat' (first | split at failed | dsimp only at failed)
            all_goals first | (cases failed; trivial) | cases failed
          · trivial
        · rename_i passed
          split
          · rename_i active
            have rows := (oldSteps_rows catalog reached position old children parents false).with_eq
            refine ResultHolds.bind (rows.imp (fun _ pair => pair) (fun stop undescribed => undescribed ▸ ⟨trivial, trivial⟩))
              fun before pair => afterOldStepsOk reached before reachedGood stillThere passed pair.1 ?_
            simpa only [active, ite_true] using pair.2
          · rename_i inactive
            exact afterOldStepsOk reached reached reachedGood stillThere passed rfl (by simp only [inactive]; rfl)
    have afterAliasOk : ∀ resumed : Unit, ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog) (afterAlias resumed) := by
      intro _
      dsimp only [afterAlias]
      split
      · trivial
      · exact afterChecksOk ()
    split
    · trivial
    · exact afterAliasOk ()
  all_goals exact good

end Belay.Sqlite.Model
