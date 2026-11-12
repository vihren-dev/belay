import Belay.Sqlite.Model.Schema.Rows.KeysUniqueFrame
import Belay.Sqlite.Model.Schema.Rows.TableAtomFrames
import Belay.Sqlite.Model.Schema.Dispatch.StatementStep

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every catalog, object, position, table entry and key: if the key is a unique key of the
position in the catalog with the object appended ({name}`Catalog.uniqueKeys`), it is a unique
key of the position in the catalog, or the object is a unique index on the position and the key
is its key ({name}`CatalogIndex.uniqueKey`). Proof sketch: the keys of the appended catalog are
the old keys followed by the key of the object, which is present only for a unique index on the
position. -/
theorem Catalog.mem_uniqueKeys_append {catalog : Catalog} {object : CatalogObject} {position : Nat}
    {shape : CatalogTable} {key : UniqueKey} (member : key ∈ (catalog ++ [object]).uniqueKeys position shape) :
    key ∈ catalog.uniqueKeys position shape ∨ ∃ index, object.entry = .index index ∧ index.table = position ∧
      index.unique = true ∧ key = index.uniqueKey := by
  unfold Catalog.uniqueKeys at member ⊢
  rw [List.filterMap_append, ← List.append_assoc, List.mem_append] at member
  rcases member with old | new
  · exact .inl old
  · refine .inr ?_
    simp only [List.filterMap_cons, List.filterMap_nil] at new
    cases entry : object.entry with
    | table _ | view _ | trigger _ => simp [entry] at new
    | index index =>
      simp only [entry] at new
      by_cases on : index.table = position ∧ index.unique = true
      · simp only [on, beq_self_eq_true, Bool.and_self, ↓reduceIte, List.mem_singleton] at new
        exact ⟨index, rfl, on.1, on.2, new⟩
      · have off : (index.table == position && index.unique) = false := by
          simpa [Bool.and_eq_true, beq_iff_eq] using on
        simp [off] at new

/-- For every database whose row lists match its catalog and object: if the database satisfies
{name}`Database.KeysUnique`, and when the object is a unique index on a table its rows have no
two rows that conflict on its key, then the database with the object and an empty row list
appended satisfies {name}`Database.KeysUnique`. Proof sketch: a table with rows is a table of
the database ({name}`Database.table_append_cases`), and each of its keys is an old key or the
key of the new index ({name}`Catalog.mem_uniqueKeys_append`). -/
theorem Database.KeysUnique.append {database : Database} (unique : database.KeysUnique)
    (aligned : database.rows.length = database.catalog.length) (object : CatalogObject)
    (newKey : ∀ index table, object.entry = .index index → index.unique = true → database.table index.table = some table →
      table.rows.Pairwise fun first second => LiteralData.keyEqual index.uniqueKey first second = false) :
    ({ catalog := database.catalog ++ [object], rows := database.rows ++ [[]] } : Database).KeysUnique := by
  intro position table present
  rcases Database.table_append_cases aligned object present with old | empty
  · intro key member
    rcases Catalog.mem_uniqueKeys_append member with kept | ⟨index, entry, on, isUnique, same⟩
    · exact unique position table old key kept
    · subst same on
      exact newKey index table entry isUnique old
  · intro key _
    rw [empty]
    exact List.Pairwise.nil

end Belay.Sqlite.Model
