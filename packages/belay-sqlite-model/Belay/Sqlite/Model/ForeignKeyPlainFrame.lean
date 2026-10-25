import Belay.Sqlite.Model.ForeignKeyCounter
import Belay.Sqlite.Model.ForeignKeyCountRows
import Belay.Sqlite.Model.AdmittedRowsOnly

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Every selected foreign-key link has another child table, and every located parent
has another position than the target. Missing and mismatched parents impose no parent
condition. No links makes this true. Use this sufficient footprint condition for plain
writes with enforcement off; the execution API still permits writes within the footprint. -/
def Catalog.ForeignKeyOutside (catalog : Catalog) (target : Nat) : Prop :=
  ∀ link ∈ catalog.foreignKeyLinks, link.child ≠ target ∧
    ∀ parent key, link.parent = .located parent key → parent ≠ target

/-- For any database, rows and target outside all selected FK child/parent reads,
replacing the target rows leaves the total violation count unchanged. No admission or
uniqueness premise is needed. Proof sketch: each link reads identical child rows and its
satisfaction test reads identical parent rows; sum the identical counts. -/
theorem Database.foreignKeyViolations_setRows_outside (database : Database) (target : Nat) (rows : List Row)
    (outside : database.catalog.ForeignKeyOutside target) :
    (database.setRows target rows).foreignKeyViolations = database.foreignKeyViolations := by
  unfold Database.foreignKeyViolations
  apply congrArg List.sum
  apply List.map_congr_left
  intro link member
  have cells : (database.setRows target rows).rowsAt link.child = database.rowsAt link.child := by
    simp only [Database.rowsAt, database.table_setRows_other rows (outside link member).1]
  rw [cells]
  apply List.countP_congr
  intro row _
  rw [link.satisfied_setRows_other database target rows row (outside link member).2]

/-- For any database with valid selected row references, an effect database that only
replaces rows outside the FK footprint retains valid selected references. A result equal
to the input needs no write reasoning. Proof sketch: split the rows-only frame and use
zero-count correspondence with the exact outside-footprint count frame. -/
theorem Database.RowReferencesHold.rowsOnlyAt {database after : Database} {target : Nat}
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (outside : database.catalog.ForeignKeyOutside target) (only : database.RowsOnlyAt target after) :
    after.RowReferencesHold after.catalog.foreignKeyMapping := by
  rcases only with rfl | ⟨_, rows, _, rfl⟩
  · exact holds
  · apply (Database.foreignKeyViolations_zero _).mp
    rw [database.foreignKeyViolations_setRows_outside target rows outside]
    exact database.foreignKeyViolations_zero.mpr holds

end Belay.Sqlite.Model
