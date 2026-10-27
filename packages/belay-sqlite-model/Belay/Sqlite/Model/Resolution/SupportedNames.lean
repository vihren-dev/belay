import Belay.Sqlite.Model.Database
import Belay.Sqlite.Model.Resolution.Catalog

set_option doc.verso true

/-! The names of a supported catalog (ADR 0022, D3): {lit}`Catalog.supported` holds exactly when the folded
names are unique and every object is supported. The laws are below the resolver of a rename, which proves that
the catalog after it keeps unique names from the test of {lit}`Catalog.supported` that it ends with. -/

namespace Belay.Sqlite.Model

/-- For every list: the list that {lit}`List.eraseDups` gives is not
longer than the list, and it has the length of the list exactly when the list has no duplicate.
Proof sketch: strong induction on the length. The head stays; the tail loses the elements equal to
the head, which leaves a list that is shorter than the tail, or equal to it exactly when the head
is not in the tail. -/
theorem length_eraseDups_iff {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (size : Nat) (items : List α), items.length = size →
      items.eraseDups.length ≤ items.length ∧ (items.eraseDups.length = items.length ↔ items.Nodup) := by
  intro size
  induction size using Nat.strongRecOn with
  | _ size ih =>
    intro items hsize
    cases items with
    | nil => simp
    | cons head tail =>
      have smaller : (tail.filter fun item => !item == head).length < size := by
        have := List.length_filter_le (fun item => !item == head) tail
        simp only [List.length_cons] at hsize
        omega
      obtain ⟨le, iff⟩ := ih _ smaller _ rfl
      have bound := List.length_filter_le (fun item => !item == head) tail
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      refine ⟨by omega, ?_⟩
      constructor
      · intro equal
        have whole : (tail.filter fun item => !item == head).length = tail.length := by omega
        have all := List.length_filter_eq_length_iff.mp whole
        have same : (tail.filter fun item => !item == head) = tail := List.filter_eq_self.mpr all
        have free : tail.Nodup := by
          have := iff.mp (by omega)
          rwa [same] at this
        refine List.nodup_cons.mpr ⟨fun inside => ?_, free⟩
        have := all head inside
        simp at this
      · intro nodup
        obtain ⟨absent, free⟩ := List.nodup_cons.mp nodup
        have same : (tail.filter fun item => !item == head) = tail :=
          List.filter_eq_self.mpr fun item inside => by
            simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
            exact fun equal => absent (equal ▸ inside)
        have equal := iff.mpr (by rwa [same])
        have lengths : (tail.filter fun item => !item == head).length = tail.length := by rw [same]
        omega

/-- For every catalog, the number of folded names is the number of tables, views and indexes. Proof sketch:
{lit}`List.map` keeps the length. -/
theorem Catalog.length_foldedNames (catalog : Catalog) :
    catalog.foldedNames.length = (catalog.filter (!·.isTrigger)).length := by
  simp [Catalog.foldedNames]

/-- For every limits and catalog, {name}`Catalog.supported` holds exactly when the folded names of
the catalog are unique ({name}`Catalog.NamesUnique`) and every object is supported under the
catalog ({name}`CatalogObject.supported`). Proof sketch: the number of names without duplicates
equals the number of names exactly when there is no duplicate ({name}`length_eraseDups_iff`). -/
theorem Catalog.supported_iff (limits : Limits) (catalog : Catalog) :
    catalog.supported limits = true ↔
      catalog.NamesUnique ∧ ∀ object ∈ catalog, object.supported limits catalog = true := by
  unfold Catalog.supported Catalog.NamesUnique
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  rw [← Catalog.length_foldedNames]
  exact and_congr_left' (length_eraseDups_iff _ _ rfl).2

end Belay.Sqlite.Model
