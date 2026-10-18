import Belay.Sqlite.DatabaseFacts

set_option doc.verso true

/-! Writes that store rows: {name}`Belay.Sqlite.Database.setRows` keeps conformance when
the new rows are valid, and writes to distinct positions commute. -/

namespace Belay.Sqlite

/-- For every conforming database, position, table in its view and rows: if the table with
the rows satisfies {name}`Table.Valid`, then storing the rows at the position
({name}`Database.setRows`) conforms to the same catalog. Use this for one-table writes.
The proof separates the changed position from the others. -/
theorem Conforms.setRows {database : Database} {position : Nat} {table : Table} {rows : List Row}
    (conforms : Conforms profile catalog database) (present : database.table position = some table)
    (valid : ({ table with rows } : Table).Valid) : Conforms profile catalog (database.setRows position rows) := by
  obtain ⟨same, catalogValid, length, each⟩ := conforms
  subst same
  have found : database.catalog.tableAt position = some table.shape := by
    cases h : database.catalog.tableAt position with
    | none => simp [Database.table, h] at present
    | some shape =>
      simp only [Database.table, h, Option.map_some, Option.some.injEq] at present
      rw [← present]
  have below : position < database.rows.length := by
    unfold Catalog.tableAt at found
    cases h : database.catalog[position]? with
    | none => simp [h] at found
    | some _ => exact length ▸ (List.getElem?_eq_some_iff.mp h).1
  refine ⟨rfl, catalogValid, by simp [Database.setRows, length], fun other => ⟨?_, ?_⟩⟩
  · intro absent
    change database.catalog.tableAt other = none at absent
    by_cases equal : other = position
    · subst other
      simp [absent] at found
    · simpa [Database.setRows, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm equal)] using
        (each other).1 absent
  · intro result found
    by_cases equal : other = position
    · subst other
      rw [Database.table_setRows rows present below] at found
      cases found
      exact valid
    · rw [Database.table_setRows_other database rows equal] at found
      exact (each other).2 result found

/-- For every database, two distinct positions and two row lists, storing the rows in
either order gives the same database. Use this equality for independent writes. Proof
sketch: only the row lists differ, and {lit}`List.set` at distinct positions commutes. -/
theorem Database.setRows_comm (database : Database) (first second : Nat)
    (firstRows secondRows : List Row) (different : first ≠ second) :
    (database.setRows first firstRows).setRows second secondRows =
      (database.setRows second secondRows).setRows first firstRows := by
  simp only [Database.setRows, Database.mk.injEq, true_and]
  exact List.set_comm _ _ different

end Belay.Sqlite
