import Belay.Sqlite.Model.KeysUniqueRowDelete
import Belay.Sqlite.Model.KeysUniqueUpsert
import Belay.Sqlite.Model.RowInsert

set_option doc.verso true

/-! The insert of a row keeps the invariant of the row engine for the atom "keys unique"
(ADR 0022, D3, slice 2): a failed constraint skips the row or stops with the state, REPLACE
deletes rows, and the write stores the table that {lit}`LiteralData.checkedRow` passed, whose
keys are the keys of the written position. -/

namespace Belay.Sqlite.Model

/-- For every catalog, state and algorithm: if the state satisfies {name}`KeyState.KeysUnique`,
the result of {name}`failedRow` keeps the invariant of the row engine. Proof sketch: IGNORE keeps
the state, FAIL and ROLLBACK stop with it, and the other algorithms carry no state. -/
theorem failedRow_keysUnique {catalog : Catalog} {state : KeyState} (unique : state.KeysUnique catalog)
    (algorithm : ConflictAlgorithm) :
    ResultHolds (KeyState.KeysUnique catalog) (KeyStop.KeysUnique catalog) (failedRow state algorithm) := by
  cases algorithm <;> first | exact unique | trivial

/-- For every catalog, state, position and table: if the database of the state has the table at
the position, the catalog has the table's entry there. Proof sketch: the definition of
{name}`Database.table`. -/
theorem KeyState.table_shape {catalog : Catalog} {state : KeyState} {position : Nat} {table : Table}
    (found : (state.database catalog).table position = some table) : catalog.tableAt position = some table.shape := by
  obtain ⟨_, atShape, same⟩ := Option.map_eq_some_iff.mp found
  rw [← same]
  exact atShape

/-- For every catalog, two states, target, three tables, row and written row: if the first state
satisfies {name}`KeyState.KeysUnique`, the second state has the first table at the target, and
{name}`LiteralData.checkedRow` with the unique keys of the first table's entry passes the second
table with the row appended and gives the third table, then the first state with the third table's rows at the target satisfies
{name}`KeyState.KeysUnique`. This is the write of {name}`insertRow`. Proof sketch: the first
table and the table of the first state at the target have the entry of the catalog there
({name}`KeyState.table_shape`), so the keys are the keys of the written table ({name}`LiteralData.checkedRow_keysUnique`). -/
theorem insertWrite_keysUnique {catalog : Catalog} {state earlier : KeyState} {target : Nat} {table current next : Table}
    {proposed : Row} {written : Option Row} (unique : state.KeysUnique catalog)
    (earlierFound : (earlier.database catalog).table target = some table)
    (passed : LiteralData.checkedRow (catalog.uniqueKeys target table.shape)
      { shape := current.shape, rows := current.rows ++ [proposed] } proposed = .ok (next, written)) :
    (state.changeRows target fun _ => next.rows).KeysUnique catalog := by
  refine KeyState.keysUnique_changeRows unique fun other otherFound => ?_
  have sameShape : table.shape = other.shape := by
    have first := KeyState.table_shape earlierFound
    rw [KeyState.table_shape otherFound, Option.some.injEq] at first
    exact first.symm
  rw [← sameShape]
  exact (LiteralData.checkedRow_keysUnique passed : next.KeysUnique _)

/-- For every catalog, links, nested run, frame, target, policy, clauses, flags, state and
values: if the nested run keeps the invariant ({name}`NestedRun.KeepsKeys`) and the state
satisfies {name}`KeyState.KeysUnique`, the result of {name}`insertRow` keeps the invariant.
Proof sketch: the join points of the definition are proved in turn, from the last: the programs
keep the invariant ({name}`runPrograms_keysUnique`), a failed constraint is
{name}`failedRow_keysUnique`, DO NOTHING keeps the state, the rows that REPLACE deletes are
{name}`deleteRow_keysUnique`, the foreign-key steps keep the rows ({name}`newSteps_rows`), and the
write is {name}`insertWrite_keysUnique`. -/
theorem insertRow_keysUnique {catalog : Catalog} {links : List ForeignKeyLink} {nested : NestedRun}
    (keeps : nested.KeepsKeys catalog) (frame : RowFrame) (target : Nat) (policy : Resolved.ConflictPolicy)
    (clauses : List Resolved.ConflictClause) (multiWrite record : Bool) {state : KeyState}
    (unique : state.KeysUnique catalog) (values : List Value) :
    ResultHolds (KeyState.KeysUnique catalog) (KeyStop.KeysUnique catalog)
      (insertRow catalog links nested frame target policy clauses multiWrite record state values) := by
  unfold insertRow
  split
  · rename_i table found
    extract_lets afterTypes afterAlias
    have afterTypesOk : ∀ resumed : Unit, ResultHolds (KeyState.KeysUnique catalog) (KeyStop.KeysUnique catalog)
        (afterTypes resumed) := by
      intro _
      dsimp (config := { zeta := false }) only [afterTypes]
      refine ResultHolds.bind (good := fun reached : KeyState × Bool => reached.1.KeysUnique catalog)
        (runPrograms_keysUnique keeps _ _ _ _ _ unique) fun reached good => ?_
      obtain ⟨reachedState, ended⟩ := reached
      split
      · exact good
      · split
        · rename_i current currentFound
          extract_lets keys proposed replaced afterCount afterClause afterChecks afterBounded
          have afterCountOk : ∀ resumed : Unit, ResultHolds (KeyState.KeysUnique catalog) (KeyStop.KeysUnique catalog)
              (afterCount resumed) := by
            intro _
            dsimp only [afterCount]
            refine ResultHolds.bind (ResultHolds.foldlM (good := KeyState.KeysUnique catalog) (fun reached row held =>
              deleteRow_keysUnique keeps { frame with algorithm := some .replace } target false false frame.recursive held row.rowid) replaced _ good)
                fun deleted deletedGood => ?_
            refine ResultHolds.bind ((newSteps_rows _ _ _ _ _ _ _ _ _).keysUnique_of_rows deletedGood)
              fun checked checkedGood => ?_
            split
            · split
              · trivial
              · rename_i next written passed
                exact ResultHolds.bind (runPrograms_keysUnique keeps _ _ _ _ _
                  (KeyState.keysUnique_of_rows rfl (insertWrite_keysUnique checkedGood currentFound passed)))
                  fun _ reached => reached
            · trivial
          have afterClauseOk : ∀ resumed : Unit, ResultHolds (KeyState.KeysUnique catalog) (KeyStop.KeysUnique catalog)
              (afterClause resumed) := by
            intro _
            dsimp only [afterClause]
            split
            · exact failedRow_keysUnique good _
            · split
              · trivial
              · exact afterCountOk ()
          have afterChecksOk : ∀ resumed : Unit, ResultHolds (KeyState.KeysUnique catalog) (KeyStop.KeysUnique catalog)
              (afterChecks resumed) := by
            intro _
            dsimp only [afterChecks]
            split
            · exact failedRow_keysUnique good _
            · split
              · split
                · exact good
                · trivial
              · exact afterClauseOk ()
          have afterBoundedOk : ∀ resumed : Unit, ResultHolds (KeyState.KeysUnique catalog) (KeyStop.KeysUnique catalog)
              (afterBounded resumed) := by
            intro _
            dsimp only [afterBounded]
            split
            · exact failedRow_keysUnique good _
            · split
              · trivial
              · exact afterChecksOk ()
          split
          · trivial
          · exact afterBoundedOk ()
        · trivial
    have afterAliasOk : ∀ resumed : Unit, ResultHolds (KeyState.KeysUnique catalog) (KeyStop.KeysUnique catalog)
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
