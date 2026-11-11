import Belay.Sqlite.Schema.Dispatch.SqlTableOrigins

set_option doc.verso true

/-! Where the {lit}`CREATE TABLE` of a table is written in the Lean source, so that a table name
in a later {lit}`sql!` can navigate to it. A {lit}`db!` term records the places in a surface
environment extension, keyed by the declaration that holds the term, outside the database value
and the script value. A later file reads the entries of its imports from the same extension.

A record applies to a database term only when the value of the declaration holds the literal
that {lit}`db!` built, compared by {name}`Lean.Expr.hash`. The proof argument is not compared,
because Lean may replace a nested proof by a lemma when it adds the declaration. So a declaration
that computes its database from the term, or from any other term, has no origin: the editor omits
the jump instead of guessing. -/

namespace Belay.Sqlite

open Lean Elab Term Belay.Sqlite.Model Translation

/-- Whether the statement is {lit}`ROLLBACK`, which may undo any creation of a table. -/
def isRollback : Syntax.Statement → Bool
  | .rollback => true
  | .createView .. | .createTable .. | .createIndex .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn .. | .dropTable .. | .dropView ..
  | .dropIndex .. | .begin | .commit | .insert .. | .insertSelect .. | .update .. | .delete .. | .select .. | .pragma _
  | .createTrigger .. | .dropTrigger .. => false

/-- The places after one more statement of a script: a {lit}`CREATE TABLE` replaces the place of
its name, a {lit}`CREATE TABLE IF NOT EXISTS` keeps the places (it may do nothing, and a place of
it could be wrong, so a table that it creates has no place), a {lit}`DROP TABLE` removes it, and {lit}`ALTER TABLE a RENAME TO b` moves the place of
{lit}`a` to the name {lit}`b` (the table that the script created keeps its {lit}`CREATE TABLE`) and
removes any place of {lit}`b`. Every other statement keeps the places, also {lit}`DROP COLUMN`, which does
not change the identity of the table. -/
def stepCreatedSlots (bytes : ByteArray) (slots : List TableSlot) (item : Located Syntax.Statement) :
    List TableSlot :=
  match item.value with
  | .createTable _ _ _ _ true => slots
  | .createTable name _ _ _ false =>
    slots.filter (·.name.folded != name.folded) ++ (slotAt? bytes item.span [0] name).toList
  | .dropTable name _ => slots.filter (·.name.folded != name.folded)
  | .renameTable name newName =>
    slots.filter (fun slot => slot.name.folded != name.folded && slot.name.folded != newName.folded) ++
      (slots.filter (·.name.folded == name.folded)).map fun slot => { slot with name := newName }
  | .createView .. | .createIndex .. | .addColumn .. | .renameColumn .. | .dropColumn .. | .dropView .. | .dropIndex .. | .begin | .commit
  | .rollback | .insert .. | .insertSelect .. | .update .. | .delete .. | .select .. | .pragma _ | .createTrigger ..
  | .dropTrigger .. => slots

/-- Where the origin of each table name of a script comes from, as the script has changed the names
so far: the table of the database at the start whose origin applies, or none when the script created
the table. A name that no entry holds still names the table of the database at the start. The
newest entry comes first. -/
abbrev OriginSources := List (List UInt8 × Option Identifier)

/-- The table of the database at the start whose origin the name has: itself when no statement of the
script changed the name, another table after a rename, and none after a creation. -/
def originSource (sources : OriginSources) (name : Identifier) : Option Identifier :=
  match sources.lookup name.folded with
  | some source => source
  | none => some name

/-- The sources after one more statement of a script: a {lit}`CREATE TABLE` or {lit}`DROP TABLE` leaves the
name without an origin, because the table is then not the one that the database had at the start (also
{lit}`CREATE TABLE IF NOT EXISTS`, which may or may not create it), and
{lit}`ALTER TABLE a RENAME TO b` gives {lit}`b` the source of {lit}`a` and leaves {lit}`a` without one.
{lit}`ROLLBACK` may undo any of these changes, so it leaves every name that an earlier statement changed
without an origin; a name that no statement changed keeps its table. Every other statement keeps the
sources, also {lit}`DROP COLUMN`. -/
def stepOriginSources (sources : OriginSources) : Syntax.Statement → OriginSources
  | .createTable name .. | .dropTable name _ => (name.folded, none) :: sources
  | .renameTable name newName => (newName.folded, originSource sources name) :: (name.folded, none) :: sources
  | .rollback => sources.map fun (name, _) => (name, none)
  | .createView .. | .createIndex .. | .addColumn .. | .renameColumn .. | .dropColumn .. | .dropView .. | .dropIndex .. | .begin | .commit
  | .insert .. | .insertSelect .. | .update .. | .delete .. | .select .. | .pragma _ | .createTrigger ..
  | .dropTrigger .. => sources

/-- The places of the {lit}`CREATE TABLE` statements that make the tables a script leaves, in the
order of the script ({name}`stepCreatedSlots`). A script with a {lit}`ROLLBACK` gives none
({name}`isRollback`). -/
def createdTableSlots (bytes : ByteArray) (items : List (Located Syntax.Statement)) : List TableSlot :=
  if items.any (isRollback ·.value) then [] else items.foldl (stepCreatedSlots bytes) []

/-- Record the origins of the tables that a {lit}`db!` script leaves, for the declaration that
holds the term. A place enters the record only when the source maps its bytes exactly
({name}`SqlEditorSource.identifier?`) and the final catalog has the table. Nothing is recorded
outside a declaration, such as {lit}`#eval db! r"..."`. -/
def registerTableOrigins (source : SqlEditorSource) (items : List (Located Syntax.Statement))
    (catalog : Catalog) (database : Expr) : TermElabM Unit := do
  let some declaration ← getDeclName? | return
  let some literal := databaseLiteral? database | return
  let file ← getFileMap
  let module ← getMainModule
  let origins := (createdTableSlots source.text.toUTF8 items).filterMap fun slot => do
    let _ ← catalog.findTable slot.name
    let identifier ← source.identifier? file slot.start slot.stop .anonymous
    let range ← identifier.getRange?
    some { table := slot.name.folded,
           location := { module, range := .ofStringPositions file range.start range.stop } : TableOrigin }
  modifyEnv fun environment =>
    tableOriginsExtension.addEntry environment { declaration, literalHash := literal.hash, origins := origins.toArray }

end Belay.Sqlite
