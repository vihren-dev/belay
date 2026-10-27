import Belay.Sqlite.Model.Resolution.ColumnDropExpr
import Belay.Sqlite.Model.Resolution.Keys

set_option doc.verso true

/-! The keys of a table and of its indexes after ALTER TABLE DROP COLUMN: every column position moves as
{lit}`dropPosition` says. -/

namespace Belay.Sqlite.Model

/-- The key term with its column position changed for the drop of the column at {lit}`index`. -/
def KeyTerm.dropColumn (index : Nat) : KeyTerm → KeyTerm
  | .column position => .column (dropPosition index position)
  | .expression value => .expression (value.dropColumn index)

/-- The index key with its term changed for the drop of the column at {lit}`index`. -/
def IndexKey.dropColumn (index : Nat) (key : IndexKey) : IndexKey :=
  { key with term := key.term.dropColumn index }

/-- The unique key with its terms and its filter changed for the drop of the column at {lit}`index`. -/
def UniqueKey.dropColumn (index : Nat) (key : UniqueKey) : UniqueKey :=
  { terms := key.terms.map (·.dropColumn index), filter := key.filter.map (·.dropColumn index) }

/-- The index with its terms and its filter changed for the drop of the column at {lit}`index` of the
table at the catalog position {lit}`table`; an index of another table stays. -/
def CatalogIndex.dropColumn (table index : Nat) (definition : CatalogIndex) : CatalogIndex :=
  if definition.table = table then
    { definition with keys := definition.keys.map (·.dropColumn index),
                      filter := definition.filter.map (·.dropColumn index) }
  else definition

/-- Whether the term reads the column at {lit}`index`. -/
def KeyTerm.readsColumn (index : Nat) : KeyTerm → Bool
  | .column position => position == index
  | .expression value => value.readsColumn index

/-- Whether an index of the table at the catalog position {lit}`table` reads the column at {lit}`index` in
a key term or in its filter. An index of another table does not. -/
def CatalogIndex.readsColumn (table index : Nat) (definition : CatalogIndex) : Bool :=
  definition.table == table &&
    (definition.keys.any (·.term.readsColumn index) || (definition.filter.map (·.readsColumn index)).getD false)

/-- Whether a key reads the column at {lit}`index` in a term or in its filter. -/
def UniqueKey.readsColumn (index : Nat) (key : UniqueKey) : Bool :=
  key.terms.any (·.term.readsColumn index) || (key.filter.map (·.readsColumn index)).getD false

end Belay.Sqlite.Model
