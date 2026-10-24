import Belay.Sqlite.Model.ForeignKeySatisfied

set_option doc.verso true

/-! A supplied parent comparison for every foreign-key declaration. The mapping is total:
omitting a comparison means a missing target, rather than omitting the declaration. Row facts
can keep a mapping after a supporting index is removed; schema facts check current selection. -/

namespace Belay.Sqlite.Model

/-- The parent comparison for each child position and foreign-key declaration. Located targets
select the child columns for both NULL tests and comparison, including repeated columns.
Missing or mismatched targets use the declaration columns for NULL tests. Use
{lit}`Catalog.foreignKeyMapping` for current choices. Return {lean}`ParentLink.missing` for a
missing comparison; only NULL child keys then satisfy it. Catalog edits that move tables
require explicit transport of the positions. -/
structure ForeignKeyMapping where
  /-- The supplied parent target and comparison for a child position and declaration. -/
  parent : Nat → ForeignKey → ParentLink

/-- The mapping selected by the catalog's existing parent-key rules, including column order
and repeated columns. No independent selection algorithm is used. -/
def Catalog.foreignKeyMapping (catalog : Catalog) : ForeignKeyMapping :=
  ⟨fun _ key => catalog.parentLink key⟩

/-- The supplied link for a declared key. Parent selection supplies the located comparison
and its NULL-test projection; the original declaration supplies the fallback for an absent
comparison. The child position and declaration remain unchanged. -/
def ForeignKeyMapping.link (mapping : ForeignKeyMapping) (child : Nat) (key : ForeignKey) : ForeignKeyLink :=
  { child, key, parent := mapping.parent child key }

/-- Whether a parent target has a selected comparison. Missing tables and unsupported parent
keys return {lean}`false`. -/
def ParentLink.isLocated : ParentLink → Bool
  | .located .. => true
  | .missing | .mismatch _ => false

/-- Move a parent target with the supplied position map. Missing targets stay missing;
comparison column positions stay unchanged. Use {lean}`keptBelow []` for no removed positions. -/
def ParentLink.transport (move : Nat → Nat) : ParentLink → ParentLink
  | .located position key => .located (move position) key
  | .mismatch position => .mismatch (move position)
  | .missing => .missing

/-- For every database, link and row, if the link uses that catalog's selection, substituting
its selected mapping leaves satisfaction unchanged. Proof sketch: identify the replaced field. -/
theorem ForeignKeyMapping.selected_satisfied (database : Database) (link : ForeignKeyLink) (row : Row)
    (selected : link.parent = database.catalog.parentLink link.key) :
    (database.catalog.foreignKeyMapping.link link.child link.key).satisfied database row =
      link.satisfied database row := by
  cases link
  simp only [ForeignKeyMapping.link, Catalog.foreignKeyMapping] at *
  subst selected
  rfl

end Belay.Sqlite.Model
