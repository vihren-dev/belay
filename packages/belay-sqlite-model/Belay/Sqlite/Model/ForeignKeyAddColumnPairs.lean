import Belay.Sqlite.Model.ForeignKeyAddColumnSelection

set_option doc.verso true

/-! The columns that a selected parent key reads. They are columns of the child declaration and
of the parent table, which lets ADD COLUMN premises about a mapping follow from facts about the
declarations and the parent indexes. -/

namespace Belay.Sqlite.Model


/-- For every function, items and outputs: if mapping the items in {name}`Option` gives the outputs,
each output is the result of some item. Proof sketch: induction on the items. -/
theorem mapM_option_mem {α β} (function : α → Option β) :
    ∀ (items : List α) (outs : List β), items.mapM function = some outs →
      ∀ out ∈ outs, ∃ item ∈ items, function item = some out
  | [], outs, done, out, member => by
    simp [List.mapM_nil] at done
    subst done
    simp at member
  | item :: rest, outs, done, out, member => by
    simp only [List.mapM_cons] at done
    cases head : function item with
    | none => simp [head] at done
    | some first =>
      cases tail : rest.mapM function with
      | none => simp [head, tail] at done
      | some others =>
        simp only [head, tail] at done
        change some (first :: others) = some outs at done
        cases done
        rcases List.mem_cons.mp member with rfl | inRest
        · exact ⟨item, by simp, head⟩
        · obtain ⟨found, inItems, eq⟩ := mapM_option_mem function rest others tail out inRest
          exact ⟨found, by simp [inItems], eq⟩

/-- For every parent table, foreign key, index and pairs: if {name}`matchIndex` gives the pairs,
each pair has a child column of the key and a parent column of the table. Proof sketch: each pair
comes from one index column, which names a column of the parent and a place of the key. -/
theorem matchIndex_pairs (parent : CatalogTable) (key : ForeignKey) (index : List (Nat × Collation))
    (pairs : List (Nat × Nat)) (matched : matchIndex parent key index = some pairs) :
    ∀ pair ∈ pairs, pair.2 < parent.columns.length ∧ pair.1 ∈ key.columns := by
  intro pair member
  unfold matchIndex at matched
  split at matched
  · cases matched
  · obtain ⟨⟨column, collation⟩, _, eq⟩ := mapM_option_mem _ index pairs matched pair member
    cases definition : parent.columns[column]? with
    | none => simp [definition] at eq
    | some found =>
      simp only [definition] at eq
      simp at eq
      obtain ⟨_, eq⟩ := eq
      cases place : key.referenced.findIdx? (·.sameName found.name) with
      | none => simp [place] at eq
      | some index' =>
        cases child : key.columns[index']? with
        | none => simp [place, child] at eq
        | some value =>
          simp [place, child] at eq
          subst eq
          exact ⟨(List.getElem?_eq_some_iff.mp definition).1, List.mem_of_getElem? child⟩

/-- For every catalog, position, parent table, foreign key and pairs: if the parent key is the
columns key with the pairs, each pair has a child column of the declaration; and if the parent
selection reads only columns below the width ({name}`CatalogTable.SelectionBelow`), each pair has a
parent column below the width. Proof sketch: an implicit key zips the child columns with the positions of
a parent index, and an explicit key takes its pairs from {name}`matchIndex_pairs`. -/
theorem Catalog.parentKey_pairs (catalog : Catalog) (position : Nat) (shape : CatalogTable) (key : ForeignKey)
    (pairs : List (Nat × Nat)) (selected : catalog.parentKey position shape key = some (.columns pairs)) :
    ∀ pair ∈ pairs, pair.1 ∈ key.columns ∧ (shape.SelectionBelow catalog position → pair.2 < shape.columns.length) := by
  intro pair member
  unfold Catalog.parentKey at selected
  have rest : ∀ named : Bool, (if (key.columns.length == 1 && named) = true then some ParentKey.rowid else
      if key.referenced.isEmpty = true then
        (List.find? (fun x => x.fst) (catalog.parentIndexes position shape)).bind fun x =>
          if (x.snd.length == key.columns.length) = true then
            some (ParentKey.columns (key.columns.zip (List.map (fun x => x.fst) x.snd)))
          else none
      else Option.map ParentKey.columns
        (List.findSome? (fun x => matchIndex shape key x.snd) (catalog.parentIndexes position shape))) =
      some (ParentKey.columns pairs) →
        pair.1 ∈ key.columns ∧ (shape.SelectionBelow catalog position → pair.2 < shape.columns.length) := by
    intro named chosen
    split at chosen
    · cases chosen
    · split at chosen
      · obtain ⟨⟨flag, index⟩, found, built⟩ := Option.bind_eq_some_iff.mp chosen
        split at built
        · cases built
          have parts := List.of_mem_zip member
          obtain ⟨entry, inIndex, eq⟩ := List.mem_map.mp parts.2
          exact ⟨parts.1, fun below => eq ▸ below.2 _ (List.mem_of_find?_eq_some found) entry inIndex⟩
        · cases built
      · obtain ⟨index, found, built⟩ := Option.map_eq_some_iff.mp chosen
        cases built
        obtain ⟨⟨_, entry⟩, inIndexes, matched⟩ := List.exists_of_findSome?_eq_some found
        have fits := matchIndex_pairs shape key entry pairs matched pair member
        exact ⟨fits.2, fun _ => fits.1⟩
  cases found : shape.rowidAlias with
  | none => exact rest false (by simpa [found] using selected)
  | some alias =>
    cases referenced : key.referenced with
    | nil => exact rest true (by simpa [found, referenced] using selected)
    | cons name more =>
      cases more with
      | nil => exact rest _ (by simpa [found, referenced] using selected)
      | cons other more => exact rest false (by simpa [found, referenced] using selected)

end Belay.Sqlite.Model
