import Belay.Sqlite.Model.ForeignKeyInsertWrite
set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For any good state and conflict algorithm, the actual failed-row result obeys the
foreign-key success/stop contract. IGNORE keeps the state; FAIL keeps its bound; rollback
keeps the database facts; raw constraint errors require nothing. Proof: inspect the algorithm. -/
theorem failedRow_foreignKeyInvariant {profile : Profile} {catalog : Catalog} {state : KeyState}
    (good : KeyState.ForeignKeyInvariant profile catalog state) (algorithm : ConflictAlgorithm) :
    ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog) (failedRow state algorithm) := by
  cases algorithm <;> first | exact good | exact ⟨good.1, trivial⟩ | trivial

/-- For any good input, actual insertion preserves the foreign-key success/stop
contract if catalog comparisons hold and actual trigger programs and replacement deletions
preserve it. This includes IGNORE, partial FAIL, REPLACE and undescribed branches.
Proof sketch: compose BEFORE programs and replacement deletions, bind actual new-check
results, prove the accepted append, then compose AFTER programs. -/
theorem insertRow_counterBound {profile : Profile} {catalog : Catalog} {nested : NestedRun}
    (frame : RowFrame) (target : Nat) (policy : Resolved.ConflictPolicy)
    (clauses : List Resolved.ConflictClause) (multiWrite record : Bool)
    (facts : catalog.ForeignKeyComparisons)
    (programs : ∀ time cells state, KeyState.ForeignKeyInvariant profile catalog state →
      ResultHolds (fun pair : KeyState × Bool => KeyState.ForeignKeyInvariant profile catalog pair.1) (KeyStop.ForeignKeyInvariant profile catalog)
        (runPrograms catalog nested frame target time .insert cells state))
    (replacements : ∀ state row, KeyState.ForeignKeyInvariant profile catalog state →
      ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
        (replaceDelete catalog catalog.foreignKeyLinks nested frame target state row))
    {state : KeyState} (holds : KeyState.ForeignKeyInvariant profile catalog state) (values : List Value) :
    ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
      (insertRow catalog catalog.foreignKeyLinks nested frame target policy clauses multiWrite record state values) := by
  unfold insertRow
  split
  · rename_i table found
    extract_lets afterTypes afterAlias
    have afterTypesOk : ∀ resumed : Unit, ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
        (afterTypes resumed) := by
      intro _
      dsimp (config := { zeta := false }) only [afterTypes]
      refine ResultHolds.bind (good := fun reached : KeyState × Bool => KeyState.ForeignKeyInvariant profile catalog reached.1)
        (programs _ _ _ holds) fun reached good => ?_
      obtain ⟨reachedState, ended⟩ := reached
      split
      · exact good
      · split
        · rename_i current currentFound
          extract_lets keys proposed replaced afterCount afterClause afterChecks afterBounded
          have afterCountOk : ∀ resumed : Unit, ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
              (afterCount resumed) := by
            intro _
            dsimp only [afterCount]
            refine ResultHolds.bind (ResultHolds.foldlM (good := KeyState.ForeignKeyInvariant profile catalog) (fun reached row held =>
              replacements reached row held) replaced _ good)
                fun deleted deletedGood => ?_
            have rows := (newSteps_rows catalog deleted target proposed (childLinks catalog.foreignKeyLinks target)
              (parentLinks catalog.foreignKeyLinks target) multiWrite none []).with_eq
            refine ResultHolds.bind (rows.imp (fun _ pair => pair) (fun stop undescribed => undescribed ▸ ⟨trivial, trivial⟩))
              fun checked checkedFacts => ?_
            split
            · trivial
            · split
              · rename_i inner innerFound
                split
                · trivial
                · rename_i next written passed
                  split
                  · trivial
                  · rename_i admitted
                    exact ResultHolds.bind (programs _ _ _
                      (KeyState.foreignKeyInvariant_of_rows_counter rfl rfl (insertWrite_counterBound (KeyState.table_shape currentFound)
                        deletedGood facts checkedFacts.1 innerFound (by simpa using admitted) passed multiWrite checkedFacts.2)))
                      fun _ reached => reached
              · trivial
          have afterClauseOk : ∀ resumed : Unit, ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
              (afterClause resumed) := by
            intro _
            dsimp only [afterClause]
            split
            · exact failedRow_foreignKeyInvariant good _
            · split
              · trivial
              · exact afterCountOk ()
          have afterChecksOk : ∀ resumed : Unit, ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
              (afterChecks resumed) := by
            intro _
            dsimp only [afterChecks]
            split
            · exact failedRow_foreignKeyInvariant good _
            · split
              · split
                · exact good
                · trivial
              · exact afterClauseOk ()
          have afterBoundedOk : ∀ resumed : Unit, ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
              (afterBounded resumed) := by
            intro _
            dsimp only [afterBounded]
            split
            · exact failedRow_foreignKeyInvariant good _
            · split
              · trivial
              · exact afterChecksOk ()
          split
          · trivial
          · exact afterBoundedOk ()
        · trivial
    have afterAliasOk : ∀ resumed : Unit, ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
        (afterAlias resumed) := by
      intro _
      dsimp only [afterAlias]
      split
      · trivial
      · exact afterTypesOk ()
    split
    · trivial
    · exact afterAliasOk ()
  · trivial

end Belay.Sqlite.Model
