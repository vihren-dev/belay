import Belay.Sqlite.Model.ForeignKeyWriteConditions
import Belay.Sqlite.Model.ForeignKeyDropRows

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Enforced DROP preserves selected row references on success and partial FAIL, assuming
admission, unique keys, initial row references and the rule conditions for intermediate
row/action/trigger execution. For the actual first target, each successful implicit DELETE
must meet the separate NULL-or-retained-parent catalog frame. With no first table, the
input must meet that frame. Other error carriers require nothing. Proof sketch: apply the
actual row-engine invariant, then the independent catalog-removal frame only on success. -/
theorem dropKeys_rowReferences {profile : Profile} (rules : Resolved.WriteRules) (clock : Int)
    (positions : List Nat) {database : Database} (ready : database.ForeignKeyReady profile)
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (conditions : rules.ForeignKeyConditions profile database.catalog)
    (afterDelete : ∀ target table, positions.head? = some target → database.table target = some table → ∀ after,
      (rowsKeys rules clock target (.delete target (table.scanRows.map (·.rowid)) false true false)
        database true).effect = .ok after → after.DropForeignKeyFrame positions after.catalog.foreignKeyMapping
        (after.catalog.drop positions).foreignKeyMapping)
    (noDelete : positions.head?.bind database.table = none → database.DropForeignKeyFrame positions database.catalog.foreignKeyMapping
      (database.catalog.drop positions).foreignKeyMapping) :
    (dropKeys rules clock positions database).effect.Satisfies
      (fun after => after.RowReferencesHold after.catalog.foreignKeyMapping) := by
  have deleted := fun target table (found : database.table target = some table) =>
    rowsKeys_rowReferences rules clock target
      (.delete target (table.scanRows.map (·.rowid)) false true false) ready holds
      conditions.enforced conditions.comparisons conditions.programs conditions.actions conditions.before
      (by trivial) true none
  unfold dropKeys
  split
  · rename_i _ _ target rest table found
    dsimp only
    split
    · rename_i after ran
      apply Effect.satisfies_of_effectDatabase
      exact (deleted target table (by simpa using found) after (.inl ran)).drop_of_null_or_kept _ _
        (afterDelete target table rfl (by simpa using found) after ran)
    · exact deleted target table (by simpa using found)
  · apply Effect.satisfies_of_effectDatabase
    apply holds.drop_of_null_or_kept _ _
    apply noDelete
    rename_i source ignored option noMatch
    cases source with
    | nil => rfl
    | cons target rest =>
      simp only [List.head?, Option.bind_some]
      cases found : database.table target with
      | none => rfl
      | some table => exact (noMatch target rest table rfl found).elim

/-- Enforced resolved DROP retains selected row references in each success or partial FAIL
state under the actual DELETE conditions and the separate catalog-removal frames. Empty
or missing first targets use the input frame. Other error carriers impose nothing here.
Proof sketch: resolved execution uses exactly {name}`dropKeys_rowReferences`. -/
theorem runStatement_drop_enforced_rowReferences {profile : Profile} (rules : Resolved.WriteRules)
    (clock : Int) (counters : Counters) (parameters : List Value) (positions : List Nat)
    {database : Database} (ready : database.ForeignKeyReady profile)
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (conditions : rules.ForeignKeyConditions profile database.catalog)
    (afterDelete : ∀ target table, positions.head? = some target → database.table target = some table → ∀ after,
      (rowsKeys rules clock target (.delete target (table.scanRows.map (·.rowid)) false true false)
        database true).effect = .ok after → after.DropForeignKeyFrame positions after.catalog.foreignKeyMapping
          (after.catalog.drop positions).foreignKeyMapping)
    (noDelete : positions.head?.bind database.table = none →
      database.DropForeignKeyFrame positions database.catalog.foreignKeyMapping
        (database.catalog.drop positions).foreignKeyMapping) :
    (runStatement clock counters parameters (.drop positions (some rules)) database).effect.Satisfies
      (fun after => after.RowReferencesHold after.catalog.foreignKeyMapping) :=
  dropKeys_rowReferences rules clock positions ready holds conditions afterDelete noDelete

end Belay.Sqlite.Model
