import Belay.Sqlite.Model.ForeignKeyDdlDrop
import Belay.Sqlite.Model.ForeignKeyMappingCoverage

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Conditions on the catalog-removal stage of DROP, for supplied old and new mappings.
For every surviving declared child/key, either all current child rows have NULL under the
new mapping, or the old mapping transports and all its located parents remain. Removed
children impose nothing. Apply this to the actual implicit DELETE result when enforcement
is on; it constrains mappings and retained rows rather than assuming the final row atom. -/
def Database.DropForeignKeyFrame (database : Database) (positions : List Nat)
    (mapping transported : ForeignKeyMapping) : Prop :=
  ∀ child table, database.table child = some table → !positions.contains child →
      ∀ key ∈ table.shape.allForeignKeys,
        (∀ row ∈ table.rows, (transported.link (keptBelow positions child) key).hasNull row.values = true) ∨
        (transported.parent (keptBelow positions child) key =
          (mapping.parent child key).transport (keptBelow positions) ∧
          ∀ parent comparison, mapping.parent child key = .located parent comparison → !positions.contains parent)

/-- For every supplied mapping, dropping objects preserves row references if they hold
initially and each surviving child/key has one of two frames: all its rows have NULL under
the next mapping, or its old mapping transports and every located parent is kept. Removed
children impose nothing. The NULL case also permits removal of a referenced parent after
a successful implicit DELETE. Proof sketch: the NULL branch satisfies each row directly;
the retained-parent branch transports the old comparison through the position shift. -/
theorem Database.RowReferencesHold.drop_of_null_or_kept {database : Database} {mapping : ForeignKeyMapping}
    (holds : database.RowReferencesHold mapping) (positions : List Nat) (transported : ForeignKeyMapping)
    (frames : database.DropForeignKeyFrame positions mapping transported) :
    (database.drop positions).RowReferencesHold transported := by
  intro position table present key declared row member
  obtain ⟨old, kept, rfl, found⟩ := Database.table_drop_cases present
  rcases frames old table found kept key declared with nullable | ⟨moved, retained⟩
  · simp only [ForeignKeyLink.satisfied, nullable row member, Bool.true_or]
  · have frame : (mapping.parent old key).RowFrame (keptBelow positions) database (database.drop positions) := by
      cases selected : mapping.parent old key with
      | missing | mismatch => trivial
      | located parent comparison =>
        have parentKept := retained parent comparison selected
        exact ⟨congrArg (Option.map CatalogTable.columns) (database.catalog.tableAt_drop_kept parentKept),
          congrArg (fun table => (table.map Table.rows).getD []) (database.table_drop_kept positions parentKept)⟩
    have same : transported.link (keptBelow positions old) key =
        {mapping.link old key with
          child := keptBelow positions old
          parent := (mapping.parent old key).transport (keptBelow positions)} := by
      simp only [ForeignKeyMapping.link, moved]
    rw [same]
    exact (ForeignKeyLink.satisfied_transport database (database.drop positions) (keptBelow positions)
      (mapping.link old key) (keptBelow positions old) row frame).trans (holds old table found key declared row member)

/-- For every catalog-selected link and values, a NULL found by its selected child
projection also occurs among the declared child columns. This includes repeated parent
columns. Proof sketch: each selected position belongs to the declared child columns. -/
theorem ForeignKeyLink.hasNull_declared {catalog : Catalog} {link : ForeignKeyLink} {values : List Value}
    (selected : link.parent = catalog.parentLink link.key) (nullable : link.hasNull values = true) :
    link.key.columns.any (fun position => values.getD position .null == .null) = true := by
  cases choice : link.parent with
  | missing | mismatch => simpa only [ForeignKeyLink.hasNull, choice] using nullable
  | located parent key =>
    simp only [ForeignKeyLink.hasNull, choice, childValues, List.any_map, Function.comp_def, List.any_eq_true] at nullable
    obtain ⟨position, member, empty⟩ := nullable
    exact List.any_eq_true.mpr ⟨position, Catalog.parentLink_child_mem selected choice member, empty⟩

/-- For every link located at an empty parent and every satisfying child row, the selected
child projection contains NULL. The parent definition may be absent. Proof sketch: an
empty parent provides no matching row, so only the NULL branch can satisfy the link. -/
theorem ForeignKeyLink.hasNull_of_empty_parent {database : Database} {link : ForeignKeyLink} {row : Row}
    {parent : Nat} {key : ParentKey} (located : link.parent = .located parent key)
    (empty : database.rowsAt parent = []) (holds : link.satisfied database row = true) :
    link.hasNull row.values = true := by
  simp only [ForeignKeyLink.satisfied, located, empty] at holds
  cases found : database.catalog.tableAt parent with
  | none => simpa only [found, Bool.or_false] using holds
  | some shape =>
    simp only [found] at holds
    cases key with
    | columns pairs => simpa only [parentFound, Option.any_none, List.any_nil, Bool.or_false] using holds
    | rowid =>
      simp only [parentFound] at holds
      split at holds <;> simpa only [Option.any_none, List.any_nil, Bool.or_false] using holds

/-- For a selected link at an empty parent, every satisfying row has a declared NULL key.
Thus any next mapping with no located comparison accepts that row by its declaration fallback.
Proof sketch: emptiness forces a selected NULL; selected positions are declared positions. -/
theorem ForeignKeyLink.hasNull_unresolved_of_empty_parent {database : Database} {link next : ForeignKeyLink}
    {row : Row} {parent : Nat} {comparison : ParentKey}
    (selected : link.parent = database.catalog.parentLink link.key)
    (located : link.parent = .located parent comparison) (empty : database.rowsAt parent = [])
    (holds : link.satisfied database row = true) (sameKey : next.key = link.key)
    (unresolved : ∀ position key, next.parent ≠ .located position key) : next.hasNull row.values = true := by
  have nullable := ForeignKeyLink.hasNull_declared selected (ForeignKeyLink.hasNull_of_empty_parent located empty holds)
  cases choice : next.parent with
  | missing | mismatch => simpa only [ForeignKeyLink.hasNull, choice, sameKey] using nullable
  | located position key => exact (unresolved position key choice).elim

end Belay.Sqlite.Model
