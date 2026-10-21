import Belay.Sqlite.ForeignKeyPhases
import Belay.Sqlite.Upsert

set_option doc.verso true

/-! The rows that a DELETE or an UPDATE writes when it checks foreign keys (ADR 0018, D4), and
the writes of the actions of its keys. SQLite first finds the rows of the statement, then
writes them in rowid order, or primary-key order for a {lit}`WITHOUT ROWID` table, and skips a
row that an earlier action deleted. After a row is deleted, and after the new row of an update
is written when its parent key changes, each key that references the table runs its action
over the child rows of the old row: {lit}`CASCADE` deletes them, or for an update writes the
new parent key into them; {lit}`SET NULL` and {lit}`SET DEFAULT` write NULL or the column's
default; {lit}`RESTRICT` fails when there is a child row. The action of an update runs only
when the parent key changes ({name}`Belay.Sqlite.keyUnchanged`). Each action is a write of its own, with
the same counter, and every constraint of its rows is ABORT. -/

namespace Belay.Sqlite

/-- The rows of one DELETE or UPDATE of a table that checks foreign keys, with the rowids of
its rows in order: an UPDATE gives each row its new row and changes the positions. A write
whose rows the statement itself names records them ({name}`KeyState.written`); with
{lit}`ignore`, the DELETE of DROP TABLE, its own keys follow {name}`oldSteps`. -/
inductive RowWork where
  /-- Delete the rows. -/
  | delete (table : Nat) (rowids : List Int) (record ignore : Bool)
  /-- Update the rows, each to its new row, changing the positions. -/
  | update (table : Nat) (change : Row → Row) (changed : List Nat) (rowids : List Int) (record : Bool)

/-- The row with each position set to its value, stored with the column's affinity, its
generated columns computed and its rowid moved with its alias, as an UPDATE writes it. -/
def setCells (shape : CatalogTable) (cells : List (Nat × Value)) (row : Row) : Row :=
  let assigned := cells.foldl (fun values (position, value) =>
    values.set position (storeValue (LiteralData.positionAffinity shape.columns position) value)) row.values
  LiteralData.movedRowid shape.rowidAlias { row with values := LiteralData.generatedCells shape.columns assigned }

/-- The value that {lit}`SET DEFAULT` writes into a child column: NULL for a generated column or
a column without a default, or the default's value; none for a default that the model does not
describe there, such as a time keyword, which would make the statement read the clock. -/
def actionDefault (column : CatalogColumn) : Option Value :=
  if column.generated.isSome then some .null else match column.defaultValue with
  | none => some .null
  | some { form := .literal (.value value) _, .. } => some value
  | some { form := .literal (.hexLiteralTooBig _) _, .. } | some { form := .clock _, .. } => none

/-- The cells that an action writes into a child row: the new parent key for {lit}`CASCADE`,
NULL for {lit}`SET NULL`, the defaults for {lit}`SET DEFAULT` ({name}`actionDefault`). -/
def actionCells (child parent : CatalogTable) (link : ForeignKeyLink) (key : ParentKey) (new : Row) :
    Syntax.ForeignKeyAction → Option (List (Nat × Value))
  | .cascade => some (link.key.columns.zipIdx.map fun (position, index) =>
      (position, (parentCell parent key new (pairIndex index)).1))
  | .setNull => some (link.key.columns.map (·, .null))
  | .setDefault => link.key.columns.mapM fun position => (child.columns[position]?.bind actionDefault).map (position, ·)
  | .noAction | .restrict => some []
where
  /-- The place in the parent key's pairs of the key column at the written index. -/
  pairIndex (index : Nat) : Nat := match key with
    | .rowid => 0
    | .columns pairs => (pairs.findIdx? (·.1 == link.key.columns.getD index 0)).getD index

/-- The state after the new row of an UPDATE of a row is checked ({name}`LiteralData.checkedRow`
over the table with the old row replaced): a rowid alias that is no integer is
{lit}`datatype mismatch`, and a failed constraint fails as ABORT. -/
def checkedUpdate (catalog : Catalog) (state : KeyState) (position : Nat) (old new : Row) : Except KeyStop Unit :=
  match (state.database catalog).table position with
  | none => throw .undescribed
  | some table =>
    if LiteralData.aliasCellMismatch table.shape.rowidAlias new then throw (.error .datatypeMismatch)
    else match LiteralData.checkedRow (catalog.uniqueKeys position table.shape)
        (LiteralData.replaceRow table old new) new with
      | .ok _ => pure ()
      | .error reason => throw (.error reason)

/-- The action of a link for the old row of the parent table at the position, with the new row
of an update, where {lit}`run` runs the write of the action: nothing for {lit}`NO ACTION` or an
update that keeps the parent key; otherwise the child rows of the old row, which
{lit}`RESTRICT` refuses with a constraint failure and every other action writes. -/
def runAction (catalog : Catalog) (run : RowWork → KeyState → Except KeyStop KeyState) (link : ForeignKeyLink)
    (action : Syntax.ForeignKeyAction) (position : Nat) (old : Row) (new : Option Row) (state : KeyState) :
    Except KeyStop KeyState :=
  match link.parent, catalog.tableAt position, catalog.tableAt link.child with
  | .located _ key, some parent, some child =>
    let targets := (childRows (state.database catalog) link key position old [] false).map (·.rowid)
    let acted (state : KeyState) := { state with acted := if targets.isEmpty then state.acted else state.acted ++ [link.child] }
    if new.any (keyUnchanged parent key old ·) then pure state else
    match action, new with
    | .noAction, _ => pure state
    | .restrict, _ => if targets.isEmpty then pure state else throw (.error .constraintViolation)
    | .cascade, none => acted <$> run (.delete link.child targets false false) state
    | .cascade, some _ | .setNull, _ | .setDefault, _ =>
      match actionCells child parent link key (new.getD old) action with
      | none => throw .undescribed
      | some cells => acted <$> run (.update link.child (setCells child cells) (child.changedColumns link.key.columns)
          targets false) state
  | .located .., none, _ | .located .., some _, none | .mismatch _, _, _ | .missing, _, _ => pure state

/-- Run the work with the links of the catalog, with fuel for the depth of
the actions: each action runs with one less ({name}`runAction`), and the work is not described
without fuel, as SQLite fails beyond its trigger depth limit. An update checks its new row
({name}`checkedUpdate`) and, when it changes a key ({name}`updateLevel`), runs
{name}`oldSteps` and {name}`newSteps` for the changed keys of the table, those that reference
the table itself, and the changed parent keys; SQLite keeps the old row's record while it
checks the new row when the level is 1 and the rowid or primary key stays. -/
def runRows (catalog : Catalog) (links : List ForeignKeyLink) : Nat → RowWork → KeyState → Except KeyStop KeyState
  | 0, _, _ => throw .undescribed
  | fuel + 1, .delete position rowids record ignore, state => rowids.foldlM (fun (state : KeyState) rowid =>
      match ((state.database catalog).rowsAt position).find? (·.rowid == rowid) with
      | none => pure state
      | some row => do
        let state ← oldSteps catalog state position row (childLinks links position) (parentLinks links position) ignore
        let written := if record then state.written ++ [row] else state.written
        let state := { state.changeRows position fun rows => rows.filter (·.rowid != rowid) with written }
        (parentLinks links position).foldlM (fun state link =>
          runAction catalog (runRows catalog links fuel) link link.key.onDelete position row none state) state) state
  | fuel + 1, .update position change changed rowids record, state => rowids.foldlM (fun (state : KeyState) rowid =>
      match ((state.database catalog).rowsAt position).find? (·.rowid == rowid), catalog[position]? with
      | some old, some { name, entry := .table shape } => do
        let new := change old
        checkedUpdate catalog state position old new
        let level := updateLevel links position name shape changed
        let children := (childLinks links position).filter fun link =>
          link.key.childChanged changed || link.key.selfReferences name
        let parents := (parentLinks links position).filter (·.key.parentChanged shape changed)
        let before ← if level != 0 then oldSteps catalog state position old children parents false else pure state
        let moved := shape.rowidAlias.any changed.contains || (shape.withoutRowid && shape.primaryKey.any changed.contains)
        let stale := if level ≤ 1 && !moved then some old else none
        let removed := before.changeRows position fun rows => rows.filter (·.rowid != rowid)
        let checked ← if level != 0 then newSteps catalog removed position new children parents true stale changed
          else pure removed
        let written := if record then checked.written ++ [new] else checked.written
        let state := { checked with rows := before.rows, written }.changeRows position fun rows =>
          rows.map fun (row : Row) => if row.rowid == rowid then new else row
        parents.foldlM (fun state link =>
          runAction catalog (runRows catalog links fuel) link link.key.onUpdate position old (some new) state) state
      | none, _ | some _, some { entry := .index _, .. } | some _, none => pure state) state

end Belay.Sqlite
