import Belay.Sqlite.Model.Resolution.ParentKeys
import Belay.Sqlite.Model.Resolution.StatementPrepareError

set_option doc.verso true

/-! Which foreign keys a write processes (ADR 0018, D4), as SQLite's {lit}`fkey.c` decides it
while it prepares the write: the keys of the written table, the keys that reference it, and
the writes of their {lit}`ON DELETE` and {lit}`ON UPDATE` actions. Resolution uses it for the
prepare errors of a write, and execution for the keys that each row checks. -/

namespace Belay.Sqlite.Model

/-- The column positions that an UPDATE of the positions changes: the positions, and each
generated column whose expression reads a changed column, as SQLite's {lit}`sqlite3Update`
marks them. One pass per column settles a generated column that reads another. -/
def CatalogTable.changedColumns (table : CatalogTable) (assigned : List Nat) : List Nat :=
  table.columns.foldl (fun changed _ => table.columns.zipIdx.foldl (fun changed (column, position) =>
    if changed.contains position then changed else match column.generated with
      | some how => if changed.any how.expression.readsColumn then changed ++ [position] else changed
      | none => changed) changed) assigned

/-- Whether an UPDATE that changes the positions changes a column of the foreign key of the
table ({lit}`fkChildIsModified`). -/
def ForeignKey.childChanged (key : ForeignKey) (changed : List Nat) : Bool :=
  key.columns.any changed.contains

/-- Whether an UPDATE of the parent table that changes the positions changes a column that the
foreign key references ({lit}`fkParentIsModified`): a column whose folded name a referenced
column names, or, for a key that names no column, a column of the primary key. -/
def ForeignKey.parentChanged (key : ForeignKey) (parent : CatalogTable) (changed : List Nat) : Bool :=
  changed.any fun position => match parent.columns[position]? with
    | none => false
    | some column => if key.referenced.isEmpty then parent.primaryKey.contains position
      else key.referenced.any (·.sameName column.name)

/-- Whether the foreign key of the table with the name references the table itself
({lit}`sqlite3_stricmp` of the two names). -/
def ForeignKey.selfReferences (key : ForeignKey) (name : Identifier) : Bool := key.table.sameName name

/-- The foreign-key processing of an UPDATE of the table at the position that changes the
positions, as {lit}`sqlite3FkRequired` gives it: 2 when a changed key of the table references
the table itself, or when a changed parent key has an {lit}`ON UPDATE` action other than
{lit}`NO ACTION`; 1 for any other changed key of the table or changed parent key; 0 when the
UPDATE changes no key. -/
def updateLevel (links : List ForeignKeyLink) (position : Nat) (name : Identifier) (table : CatalogTable)
    (changed : List Nat) : Nat :=
  let children := (childLinks links position).filter (·.key.childChanged changed)
  let parents := (parentLinks links position).filter (·.key.parentChanged table changed)
  if parents.any (·.key.onUpdate != .noAction) || children.any (·.key.selfReferences name) then 2
  else if children.isEmpty && parents.isEmpty then 0 else 1

/-- A write whose foreign-key processing SQLite prepares: INSERT, with whether it writes more
than one row or may replace rows, DELETE, and UPDATE with the positions that it changes
({name}`CatalogTable.changedColumns`). -/
inductive ForeignKeyWrite where
  /-- INSERT: whether SQLite treats it as a write of several rows, and whether a REPLACE
  algorithm can delete rows. -/
  | insert (multiWrite replace : Bool)
  /-- DELETE, also of the rows that DROP TABLE or REPLACE deletes. -/
  | delete
  /-- UPDATE of the positions. -/
  | update (changed : List Nat)
  deriving Repr, DecidableEq

/-- The links whose violations a write of the table at the position counts, and the links that
SQLite locates for it, which give its prepare errors: for INSERT, the keys of the table and, for
a write of several rows, the keys that reference it, both counted and located; for DELETE, both
kinds of key; for UPDATE that changes a key ({name}`updateLevel`), the changed keys of the table
and those that reference the table itself, and the changed parent keys are counted, and every
key that references the table is located too, as SQLite reads them to choose the old columns
({lit}`sqlite3FkOldmask`). -/
def writeLinks (catalog : Catalog) (links : List ForeignKeyLink) (position : Nat) (write : ForeignKeyWrite) :
    List ForeignKeyLink × List ForeignKeyLink :=
  match catalog[position]? with
  | some { name, entry := .table table } => match write with
    | .insert multiWrite _ =>
      let counted := childLinks links position ++ (if multiWrite then parentLinks links position else [])
      (counted, counted)
    | .delete => let counted := childLinks links position ++ parentLinks links position; (counted, counted)
    | .update changed =>
      if updateLevel links position name table changed == 0 then ([], []) else
      let children := (childLinks links position).filter fun link =>
        link.key.childChanged changed || link.key.selfReferences name
      (children ++ (parentLinks links position).filter (·.key.parentChanged table changed),
        children ++ parentLinks links position)
  | some { entry := .index _, .. } | some { entry := .trigger _, .. } | none => ([], [])

/-- The links that a write of the table at the position processes ({name}`writeLinks`): those
that SQLite locates for it. -/
def processedLinks (catalog : Catalog) (links : List ForeignKeyLink) (position : Nat) (write : ForeignKeyWrite) :
    List ForeignKeyLink :=
  (writeLinks catalog links position write).2

/-- The writes that the actions of a write of the table at the position run: for DELETE, the
{lit}`ON DELETE` action of each located key that references the table; for UPDATE, the
{lit}`ON UPDATE` action of each one whose parent key changes; INSERT runs none. A
{lit}`CASCADE` of DELETE deletes child rows; a {lit}`CASCADE` of UPDATE, {lit}`SET NULL` and
{lit}`SET DEFAULT` update the child's key columns; {lit}`RESTRICT` and {lit}`NO ACTION` write
nothing. -/
def actionWrites (catalog : Catalog) (links : List ForeignKeyLink) (position : Nat) (write : ForeignKeyWrite) :
    List (Nat × ForeignKeyWrite) :=
  let childUpdate (link : ForeignKeyLink) : Nat × ForeignKeyWrite :=
    (link.child, .update (((catalog.tableAt link.child).map (·.changedColumns link.key.columns)).getD link.key.columns))
  let located (link : ForeignKeyLink) : Bool := match link.parent with
    | .located .. => true
    | .mismatch _ | .missing => false
  match catalog.tableAt position, write with
  | some _, .delete => (parentLinks links position).filterMap fun (link : ForeignKeyLink) =>
    if !located link then none else match link.key.onDelete with
    | .cascade => some (link.child, .delete)
    | .setNull | .setDefault => some (childUpdate link)
    | .restrict | .noAction => none
  | some table, .update changed => (parentLinks links position).filterMap fun (link : ForeignKeyLink) =>
    if !located link || !link.key.parentChanged table changed then none else match link.key.onUpdate with
      | .cascade | .setNull | .setDefault => some (childUpdate link)
      | .restrict | .noAction => none
  | some _, .insert .. | none, _ => []

/-- The prepare error of one processed link, if any: a parent table that does not exist is
{lit}`no such table: main.%s`, and a parent without a parent key is
{lit}`foreign key mismatch - "%w" referencing "%w"`, with the child table's name and the
parent's name as the key writes it. -/
def linkError (catalog : Catalog) (link : ForeignKeyLink) : Option PrepareError :=
  let child := ((catalog[link.child]?).map (·.name)).getD link.key.table
  match link.parent with
  | .located .. => none
  | .missing => some (.noSuchReferencedTable link.key.table)
  | .mismatch _ => some (.foreignKeyMismatch child link.key.table)

/-- The prepare error of a write and of the writes of its actions, and whether one of them
counts the violations of a key that is {lit}`DEFERRABLE INITIALLY DEFERRED` ({name}`writeLinks`). A write with {lit}`ignore`, the
DELETE of DROP TABLE, reports no error for its own links, as SQLite's {lit}`disableTriggers`
does; the writes of its actions report them. Each action write runs once, as SQLite prepares
each action once per statement; the fuel bounds the writes, and work left past the fuel gives
{lean}`true`, so that the write stays a restriction. -/
def foreignKeyIssues (catalog : Catalog) (links : List ForeignKeyLink) :
    Nat → List (Nat × ForeignKeyWrite) → List (Nat × ForeignKeyWrite × Bool) → Except PrepareError Bool
  | 0, _, work => .ok !work.isEmpty
  | _ + 1, _, [] => .ok false
  | fuel + 1, seen, (position, write, ignore) :: rest => do
    let (counted, processed) := writeLinks catalog links position write
    if !ignore then
      if let some error := processed.findSome? (linkError catalog) then throw error
    let replaced := match write with
      | .insert _ true => if (childLinks links position ++ parentLinks links position).isEmpty then [] else [(position, .delete)]
      | .insert _ false | .delete | .update _ => []
    let next := (replaced ++ actionWrites catalog links position write).filter (!seen.contains ·)
    let later ← foreignKeyIssues catalog links fuel (seen ++ next) (rest ++ next.map fun (p, w) => (p, w, false))
    return counted.any (·.key.deferred) || later

/-- The foreign-key issues of one write of the table at the position
({name}`foreignKeyIssues`), with fuel for every action write: two per key and one for the
write itself. -/
def Catalog.foreignKeyIssues (catalog : Catalog) (position : Nat) (write : ForeignKeyWrite) (ignore : Bool := false) :
    Except PrepareError Bool :=
  let links := catalog.foreignKeyLinks
  Belay.Sqlite.Model.foreignKeyIssues catalog links (2 * links.length + 2) [] [(position, write, ignore)]

end Belay.Sqlite.Model
