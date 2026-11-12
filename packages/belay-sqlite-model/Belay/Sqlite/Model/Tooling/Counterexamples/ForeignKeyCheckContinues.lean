import Belay.Sqlite.Model.Tooling.Counterexamples.ForeignKeyStatementCheck
import Belay.Sqlite.Model.Programs.Scripts.ReadOnlyFrame

set_option doc.verso true

/-! The database-wide {lit}`PRAGMA foreign_key_check` as a step that continues (ADR 0017, S6). The rows of the
pragma can be empty or not: a script that runs the pragma before it commits goes on in both cases. The
step is a read-only query, so it changes nothing. -/

namespace Belay.Sqlite.Model

/-- For every list without repeats and every function that gives nothing at the positions other than one: the
function gives at most one item over the list. Proof sketch: induction on the list; the first position gives the
only item or nothing, and the rest of the list does not repeat the position. -/
theorem filterMap_length_le_one (only : Nat) (items : Nat → Option (List (List Value))) :
    ∀ positions : List Nat, positions.Nodup → (∀ position ∈ positions, position ≠ only → items position = none) →
      (positions.filterMap items).length ≤ 1
  | [], _, _ => by simp
  | position :: rest, nodup, quiet => by
    by_cases same : position = only
    · subst same
      have none : rest.filterMap items = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro other member
        exact quiet other (List.mem_cons_of_mem _ member) (fun equal => (List.nodup_cons.mp nodup).1 (equal ▸ member))
      cases found : items position <;> simp [found, none]
    · rw [List.filterMap_cons, quiet position (List.mem_cons_self ..) same]
      exact filterMap_length_le_one only items rest (List.nodup_cons.mp nodup).2
        (fun other member => quiet other (List.mem_cons_of_mem _ member))

/-- For every database in which every table other than the one at a position gives no row of
{lit}`PRAGMA foreign_key_check` ({name}`Database.keyCheckRows`), whatever the rows of the other tables are, the
pragma of every table gives rows: the model generates them. In plain words, if at most one table has a foreign
key, the model can answer the foreign-key check of the database. Proof sketch: the tables that give rows are
among the one at the position, so the model does not meet the case of two tables
({name}`Database.foreignKeyCheckRows`). -/
theorem Database.foreignKeyCheckRows_isSome (database : Database) (only : Nat)
    (quiet : ∀ position table, position ≠ only → database.table position = some table →
      database.keyCheckRows position table = []) :
    ∃ rows, (Resolved.PragmaRows.foreignKeyCheck none).rowsOn database = some rows := by
  show ∃ rows, database.foreignKeyCheckRows none = some rows
  unfold Database.foreignKeyCheckRows
  cases blocks : database.blocks (database.checkPositions none) database.keyCheckRows with
  | nil => exact ⟨[], rfl⟩
  | cons rows rest =>
    cases rest with
    | nil => exact ⟨rows, rfl⟩
    | cons _ _ =>
      exfalso
      have short : (database.blocks (database.checkPositions none) database.keyCheckRows).length ≤ 1 := by
        unfold Database.blocks
        refine filterMap_length_le_one only _ _ (by simpa [Database.checkPositions] using List.nodup_range) ?_
        intro position _ other
        cases present : database.table position with
        | none => rfl
        | some table => simp only [Option.bind_some, quiet position table other present]
      rw [blocks] at short
      simp at short

end Belay.Sqlite.Model
