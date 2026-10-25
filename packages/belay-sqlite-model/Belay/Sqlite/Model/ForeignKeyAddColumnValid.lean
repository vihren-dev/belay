import Belay.Sqlite.Model.ForeignKeyAddColumnReads
import Belay.Sqlite.Model.AddColumnFromValid

set_option doc.verso true

/-! What a valid catalog gives to ADD COLUMN on the selection of a parent key. -/

namespace Belay.Sqlite.Model

/-- For every valid catalog, position and table at the position: the table selects its parents below
its width ({name}`CatalogTable.SelectionBelow`). Proof sketch: the rowid alias, the primary key and
the UNIQUE constraints of a supported table name columns of the table, and an index of a valid catalog
is supported for the width of its table, so each parent index names columns below the width. -/
theorem Catalog.Valid.selectionBelow {limits : Limits} {catalog : Catalog} (valid : catalog.Valid limits)
    {position : Nat} {shape : CatalogTable} (present : catalog.tableAt position = some shape) :
    shape.SelectionBelow catalog position := by
  obtain ⟨_, _, _, _, primary, unique, alias, _⟩ := (CatalogTable.supported_iff _ _).mp (valid.tableSupported present)
  refine ⟨fun place found => ?_, ?_⟩
  · obtain ⟨_, _, column, atPlace, _⟩ := alias place found
    exact (List.getElem?_eq_some_iff.mp atPlace).1
  · intro entry member pair inside
    unfold Catalog.parentIndexes at member
    simp only [List.mem_append] at member
    rcases member with (primaryEntry | uniqueEntry) | indexEntry
    · split at primaryEntry
      · simp at primaryEntry
      · rw [List.mem_singleton] at primaryEntry
        subst primaryEntry
        obtain ⟨place, inKey, rfl⟩ := List.mem_map.mp inside
        exact primary place inKey
    · obtain ⟨key, inKeys, rfl⟩ := List.mem_map.mp uniqueEntry
      obtain ⟨place, inKey, rfl⟩ := List.mem_map.mp inside
      exact (unique key inKeys).2 place inKey
    · obtain ⟨object, inObject, kept⟩ := List.mem_filterMap.mp indexEntry
      have supported := valid.object inObject
      cases entry' : object.entry with
      | table _ => simp [entry'] at kept
      | trigger _ => simp [entry'] at kept
      | index found =>
        simp only [entry'] at kept
        split at kept
        · cases kept
        · rename_i same
          obtain ⟨pairs, mapped, eq⟩ := Option.map_eq_some_iff.mp kept
          cases eq
          obtain ⟨indexKey, inKeys, built⟩ := mapM_option_mem _ found.keys pairs mapped pair inside
          simp only [CatalogObject.supported, entry', Bool.and_eq_true] at supported
          have table : found.table = position := Classical.byContradiction fun h => same (by simp [h])
          rw [table, present] at supported
          have bound : found.supported shape.columns.length = true := by simpa using supported.2
          simp only [CatalogIndex.supported, Bool.and_eq_true, List.all_eq_true, List.mem_filterMap,
            decide_eq_true_eq, forall_exists_index, and_imp] at bound
          obtain ⟨⟨⟨_, positions⟩, _⟩, _⟩ := bound
          cases term : indexKey.term with
          | expression _ => simp [term] at built
          | column place =>
            simp only [term, Option.some.injEq] at built
            subst built
            exact positions place indexKey inKeys (by rw [term])

/-- For every admitted database and target, the database meets {name}`Database.SelectionBelowAt`: if
the catalog has a table at the target, the table selects its parents below its width. A target
without a table requires nothing. Proof sketch: {name}`Catalog.Valid.selectionBelow` for the valid
catalog of an admitted database. -/
theorem Database.selectionBelowAt_of_admitted {profile : Profile} {database : Database}
    (admitted : database.Admitted profile) (target : Nat) : database.SelectionBelowAt target :=
  fun _ present => admitted.catalogSupported.selectionBelow present

end Belay.Sqlite.Model
