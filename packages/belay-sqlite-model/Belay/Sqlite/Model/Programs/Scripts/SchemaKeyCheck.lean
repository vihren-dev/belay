import Belay.Sqlite.Model.Programs.StatementRunLaws.ForeignKeyCheckContinues

set_option doc.verso true

/-! Bound the number of foreign-key result blocks using the catalog, for schema-only success. -/

namespace Belay.Sqlite.Model

/-- The unqualified foreign-key check has a modeled row order for every choice of
rows when at most one checked table has a child link. Checking a named table
inspects only that position. -/
def Catalog.keyCheckOrdered (catalog : Catalog) (table : Option Nat) : Bool :=
  let positions := table.elim (List.range catalog.length) ([·])
  (positions.filter (fun p => !(childLinks catalog.foreignKeyLinks p).isEmpty)).length ≤ 1

/-- Positions with no child links contribute no output block. The number of output
blocks is at most the number of checked positions with child links. Proof sketch:
induct on the positions and bound each table's optional contribution by one. -/
private theorem keyCheck_blocks_bound (db : Database) (positions : List Nat) :
    (db.blocks positions db.keyCheckRows).length ≤
      (positions.filter (fun p => !(childLinks db.catalog.foreignKeyLinks p).isEmpty)).length := by
  induction positions with
  | nil => simp [Database.blocks]
  | cons p rest ih =>
    by_cases empty : (childLinks db.catalog.foreignKeyLinks p).isEmpty = true
    · have links : childLinks db.catalog.foreignKeyLinks p = [] := List.isEmpty_iff.mp empty
      have nilRows (t : Table) : db.keyCheckRows p t = [] := by simp [Database.keyCheckRows, links]
      cases present : db.table p <;> simpa [Database.blocks, present, nilRows, empty] using ih
    · simp only [Database.blocks, List.filterMap_cons] at *
      simp [empty]
      split <;> simp_all <;> omega

/-- On every database whose catalog passes {name}`Catalog.keyCheckOrdered`, the
foreign-key check returns a list of rows. A row can report a violation. Proof sketch:
the catalog bound rules out two output blocks, the only unmodeled case. -/
theorem Database.keyCheckRows_modeled {db : Database} {table : Option Nat}
    (ordered : db.catalog.keyCheckOrdered table = true) :
    ∃ rows, (Resolved.PragmaRows.foreignKeyCheck table).rowsOn db = some rows := by
  have bound := keyCheck_blocks_bound db (db.checkPositions table)
  have limit : ((db.checkPositions table).filter (fun p =>
      !(childLinks db.catalog.foreignKeyLinks p).isEmpty)).length ≤ 1 := by
    cases table <;> exact of_decide_eq_true ordered
  change ∃ rows, db.foreignKeyCheckRows table = some rows
  unfold Database.foreignKeyCheckRows
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rename_i h
    rw [h] at bound
    simp at bound
    omega

end Belay.Sqlite.Model
