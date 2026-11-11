import Belay.Sqlite.Model.Schema.Rows.ForeignKeyFacts

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The child columns that a link reads: the selected projection of a located parent
({name}`childPositions`), else the declaration columns, as {name}`ForeignKeyLink.hasNull` reads
them. -/
def ForeignKeyLink.childReads (link : ForeignKeyLink) : List Nat :=
  match link.parent with
  | .located _ key => childPositions link key
  | .missing | .mismatch _ => link.key.columns

/-- Whether a parent key reads only the parent columns below the width: a rowid key reads no
column, and a key of columns reads the parent position of each pair. -/
def ParentKey.ReadsBelow (width : Nat) : ParentKey → Prop
  | .rowid => True
  | .columns pairs => ∀ pair ∈ pairs, pair.2 < width

end Belay.Sqlite.Model
