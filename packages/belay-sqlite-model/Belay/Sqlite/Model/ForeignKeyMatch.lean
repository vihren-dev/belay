import Belay.Sqlite.Model.LiteralData
import Belay.Sqlite.Model.Resolution.QueryAffinity

set_option doc.verso true

/-! How SQLite's {lit}`fkey.c` compares the key of a child row with the key of a parent row
(ADR 0018, D4). Three comparisons differ, and the model keeps each one:

* a child row looks up its parent ({lit}`fkLookupParent`): the child's values take the
  parent index's affinity and are found in the index under the parent key's collation; for a
  rowid key, a value that is no integer after NUMERIC affinity finds no row;
* a parent row finds its child rows ({lit}`fkScanChildren`) and an action finds the rows that it
  changes ({lit}`fkActionTrigger`): each pair compares as {lit}`parent = child` does, with the
  comparison affinity of the two columns and the parent column's collation;
* a new row of a table that references itself is its own parent when each child value equals
  its own parent value with no affinity and {lit}`BINARY`.

Checked natively: over {lit}`p(k TEXT UNIQUE)` and {lit}`c(x INTEGER REFERENCES p(k))` with the
rows {lit}`'1'` and {lit}`'01'` of {lit}`p` and {lit}`1` of {lit}`c`, the child finds the parent
{lit}`'1'`, but {lit}`DELETE FROM p WHERE k = '01'` fails: the scan finds the child of
{lit}`'01'` by its numeric value. -/

namespace Belay.Sqlite.Model

/-- The values of the selected child columns of a row, in parent-key order. Missing cells
read NULL. {name}`childPositions` retains duplicate selections. -/
def childValues (link : ForeignKeyLink) (key : ParentKey) (values : List Value) : List Value :=
  (childPositions link key).map (values.getD · .null)

/-- Whether a selected child key value is NULL: use {name}`childValues` for a located parent,
including repeated child columns, and the declaration's columns when no comparison is selected.
A NULL in an unused declaration column does not exempt a located key. For example, a selected
projection {lit}`[x,x]` ignores NULL in {lit}`y`, as SQLite's {lit}`OP_IsNull` checks do. -/
def ForeignKeyLink.hasNull (link : ForeignKeyLink) (values : List Value) : Bool :=
  match link.parent with
  | .located _ key => (childValues link key values).any (· == .null)
  | .missing | .mismatch _ => link.key.columns.any fun position => values.getD position .null == .null

/-- The affinity of a parent index column, as {lit}`sqlite3IndexAffinityStr` gives it: NUMERIC
for INTEGER, REAL and NUMERIC columns, and the column's own affinity otherwise. -/
def indexAffinity (column : CatalogColumn) : Affinity :=
  if numericAffinity column.affinity then .numeric else column.affinity

/-- Whether a parent row has the key of the child values for a key of columns, as the index
lookup finds it: each child value with the {name}`indexAffinity` of its parent column equals
the parent cell under the parent column's collation ({name}`LiteralData.keyCellsEqual`). -/
def indexHolds (parent : CatalogTable) (pairs : List (Nat × Nat)) (values : List Value) (row : Row) : Bool :=
  (pairs.zip values).all fun ((_, position), value) => match parent.columns[position]? with
    | none => false
    | some column => LiteralData.keyCellsEqual (row.values.getD position .null) (Value.store (indexAffinity column) value)
        column.collation

/-- Whether the rows hold a parent row for the child row's values ({lit}`fkLookupParent`): for a
rowid key, a row whose rowid is the child value with NUMERIC affinity when that is an integer
({lit}`OP_MustBeInt`); for a key of columns, a row of {name}`indexHolds`. With a new row of a
table that references itself, the row is its own parent when each child value equals its own
parent value under {lit}`BINARY` without affinity. -/
def parentFound (parent : CatalogTable) (key : ParentKey) (link : ForeignKeyLink) (values : List Value)
    (rows : List Row) (itself : Option Row) : Bool :=
  let keyed := childValues link key values
  match key with
  | .rowid => match keyed.map numericStore with
    | [.integer rowid] => itself.any (·.rowid == rowid) || rows.any (·.rowid == rowid)
    | [] | [.null] | [.real _] | [.text _] | [.blob _] | _ :: _ :: _ => false
  | .columns pairs =>
    itself.any (fun row => (pairs.zip keyed).all fun ((_, position), value) =>
      LiteralData.keyCellsEqual value (row.values.getD position .null)) ||
    rows.any (indexHolds parent pairs keyed)

/-- The value of the parent key column of a pair in a parent row, with its affinity and
collation: the rowid with INTEGER affinity for a rowid key. -/
def parentCell (parent : CatalogTable) (key : ParentKey) (row : Row) (index : Nat) : Value × Affinity × Collation :=
  match key with
  | .rowid => (.integer row.rowid, .integer, .binary)
  | .columns pairs => match pairs[index]? with
    | none => (.null, .blob, .binary)
    | some (_, position) =>
      let column := parent.columns[position]?
      (row.values.getD position .null, (column.map (·.affinity)).getD .blob, (column.map (·.collation)).getD .binary)

/-- Whether a child row belongs to a parent row ({lit}`fkScanChildren`, and the {lit}`WHERE` of
an action): for each pair, {lit}`parent = child` is true, with the comparison affinity of the
parent column and the child column ({name}`comparisonAffinity`) and the parent's collation. -/
def childMatches (child parent : CatalogTable) (link : ForeignKeyLink) (key : ParentKey) (parentRow childRow : Row) :
    Bool :=
  (childPositions link key).zipIdx.all fun ((position : Nat), (index : Nat)) =>
    let (value, affinity, collation) := parentCell parent key parentRow index
    let childAffinity := ((child.columns[position]?).map CatalogColumn.affinity).getD Affinity.blob
    let (left, right) := Resolved.comparisonOperands (comparisonAffinity (some affinity) (some childAffinity)) value
      (childRow.values.getD position .null)
    LiteralData.keyCellsEqual left right collation

/-- Whether the parent key of a parent row is unchanged by an UPDATE, as the {lit}`WHEN` of an
{lit}`ON UPDATE` action reads it: each parent cell of the old row {lit}`IS` the cell of the new
row under the parent column's collation. -/
def keyUnchanged (parent : CatalogTable) (key : ParentKey) (old new : Row) : Bool :=
  let count := match key with
    | .rowid => 1
    | .columns pairs => pairs.length
  (List.range count).all fun index =>
    let (before, _, collation) := parentCell parent key old index
    let (after, _, _) := parentCell parent key new index
    (before == .null && after == .null) || LiteralData.keyCellsEqual before after collation

end Belay.Sqlite.Model
