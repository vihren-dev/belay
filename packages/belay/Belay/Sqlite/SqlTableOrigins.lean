import Belay.Sqlite.SqlTableSlots
import Belay.Sqlite.SqlEditorSource
import Lean.Elab.DeclarationRange
import Lean.Elab.Term

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

/-- The place of the {lit}`CREATE TABLE` of one table: the table name in folded bytes
({name}`Identifier.folded`) and the source range of the written name. -/
structure TableOrigin where
  /-- The table name in folded bytes. -/
  table : List UInt8
  /-- The module and the range of the table name in the {lit}`CREATE TABLE`. -/
  location : DeclarationLocation

/-- The origins of the tables of one {lit}`db!` term: the declaration that holds the term, the
hash of the database literal in the term and one origin for each table of the final catalog with a
known place. -/
structure DatabaseOrigins where
  /-- The declaration whose value is the {lit}`db!` term. -/
  declaration : Name
  /-- The hash ({name}`Lean.Expr.hash`) of the database literal in the term that {lit}`db!` built. -/
  literalHash : UInt64
  /-- The tables with a known origin. -/
  origins : Array TableOrigin

/-- The environment extension of the origins, one entry for each declaration with a {lit}`db!`
term. Entries of imported modules are available after the import. -/
initialize tableOriginsExtension : SimplePersistentEnvExtension DatabaseOrigins (NameMap DatabaseOrigins) ←
  registerSimplePersistentEnvExtension {
    name := `Belay.Sqlite.tableOrigins
    addEntryFn := fun origins entry => origins.insert entry.declaration entry
    addImportedFn := fun imported =>
      imported.foldl (init := {}) fun origins entries =>
        entries.foldl (fun origins entry => origins.insert entry.declaration entry) origins
    asyncMode := .sync }

/-- The model database literal in a database term: the first argument of {name}`Database.mk`,
which a {lit}`db!` term holds, without a wrapper of replay metadata. -/
def databaseLiteral? (database : Expr) : Option Expr :=
  match database.consumeMData.getAppFnArgs with
  | (``Database.mk, #[literal, _]) => some literal
  | _ => none

/-- Whether the statement is {lit}`ROLLBACK`, which may undo any creation of a table. -/
def isRollback : Syntax.Statement → Bool
  | .rollback => true
  | .createView .. | .createTable .. | .createIndex .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn .. | .dropTable .. | .dropView ..
  | .dropIndex .. | .begin | .commit | .insert .. | .insertSelect .. | .update .. | .delete .. | .select .. | .pragma _
  | .createTrigger .. | .dropTrigger .. => false

/-- The places after one more statement of a script: a {lit}`CREATE TABLE` replaces the place of
its name, a {lit}`DROP TABLE` removes it, and {lit}`ALTER TABLE a RENAME TO b` moves the place of
{lit}`a` to the name {lit}`b` (the table that the script created keeps its {lit}`CREATE TABLE`) and
removes any place of {lit}`b`. Every other statement keeps the places, also {lit}`DROP COLUMN`, which does
not change the identity of the table. -/
def stepCreatedSlots (bytes : ByteArray) (slots : List TableSlot) (item : Located Syntax.Statement) :
    List TableSlot :=
  match item.value with
  | .createTable name .. =>
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
name without an origin, because the table is then not the one that the database had at the start, and
{lit}`ALTER TABLE a RENAME TO b` gives {lit}`b` the source of {lit}`a` and leaves {lit}`a` without one.
Every other statement keeps the sources, also {lit}`DROP COLUMN`. -/
def stepOriginSources (sources : OriginSources) : Syntax.Statement → OriginSources
  | .createTable name .. | .dropTable name _ => (name.folded, none) :: sources
  | .renameTable name newName => (newName.folded, originSource sources name) :: (name.folded, none) :: sources
  | .createView .. | .createIndex .. | .addColumn .. | .renameColumn .. | .dropColumn .. | .dropView .. | .dropIndex .. | .begin | .commit
  | .rollback | .insert .. | .insertSelect .. | .update .. | .delete .. | .select .. | .pragma _ | .createTrigger ..
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

/-- The longest chain of constants that stand for each other ({lit}`def c := b`, {lit}`def b := a`)
that {lit}`originsOf` follows from the database term to a {lit}`db!` declaration. A chain that is
longer gives no origin, so the table names of that database get no jump. -/
def aliasChainLimit : Nat := 64

/-- The origins of the database that a term names: the term is a constant, or constants that
stand for each other ({lit}`def b := a`), whose value holds the literal that a {lit}`db!` recorded. A
term of any other form, and a declaration with a changed value, has none. The fuel bounds the
chain of constants; use {name}`aliasChainLimit`. -/
def originsOf (environment : Environment) : Nat → Expr → Option DatabaseOrigins
  | 0, _ => none
  | fuel + 1, database =>
    match database.consumeMData with
    | .const name _ =>
      let value? := (environment.find? name).bind (·.value?)
      match (tableOriginsExtension.getState environment).find? name with
      | some entry =>
        if (value?.bind databaseLiteral?).any (·.hash == entry.literalHash) then some entry else none
      | none => value?.bind (originsOf environment fuel)
    | _ => none

end Belay.Sqlite
