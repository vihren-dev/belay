import Belay.Sqlite.SqlTableInfo
import Belay.Sqlite.SqlTableSlots
import Belay.Sqlite.SqlStatementContexts
import Belay.Sqlite.SqlTableDescription
import Belay.Sqlite.SqlTableOrigins

set_option doc.verso true

/-! The entry point that gives located SQL its editor information (the editor task, part 2a). A
caller supplies the located statements, the mapping of the SQL bytes to the Lean source
({lit}`SqlEditorSource`), what it knows about the database ({lit}`KnownDatabase`) and the
context of each statement ({lit}`StatementContext`). The module resolves no name itself: it finds
the table names that the syntax fixes ({lit}`tableSlotsOf`), asks the catalog of the statement's
context, and emits one hover for each place. {lit}`sql!` and later the SQL files and
documentation blocks call it. -/

namespace Belay.Sqlite

open Lean Elab Term Belay.Sqlite.Model Translation

/-- What a caller knows about the database that a script starts on. Use the default value for
a database whose declaration and origins are unknown. -/
structure KnownDatabase where
  /-- The declaration that names the database term, shown in the hover. -/
  owner : Option Name := none
  /-- Where the {lit}`CREATE TABLE` of a table of the database at the start is written, when the
  caller knows it. A caller that knows no origin keeps the default. -/
  origin? : Identifier → Option DeclarationLocation := fun _ => none

/-- What the editor knows about the database that a term names: the origins recorded for the
declaration that holds a {lit}`db!` term ({name}`originsOf`), and the declaration as the owner.
A term with no recorded origin, such as a computed database, keeps its constant as the owner and
gets no jump. -/
def KnownDatabase.ofTerm (environment : Lean.Environment) (term : Lean.Expr) : KnownDatabase :=
  match originsOf environment aliasChainLimit term with
  | some entry =>
    { owner := some entry.declaration,
      origin? := fun name => (entry.origins.find? (·.table == name.folded)).map (·.location) }
  | none => { owner := term.consumeMData.constName? }

/-- The hover text and the origin of the table at a place of a statement: nothing when the
context's catalog has no table of that name. The origin is dropped when an earlier statement of
the script created or dropped a table of the name ({name}`replacedTable?`),
because the table is then not the one that the database had at the start. -/
def slotInformation (known : KnownDatabase) (replaced : List (List UInt8)) (context : StatementContext)
    (slot : TableSlot) : Option (String × Option DeclarationLocation) := do
  let (position, table) ← context.catalog.findTable slot.name
  let rows := context.rows?.map fun rows => (rows.getD position []).length
  let location := if replaced.contains slot.name.folded then none else known.origin? slot.name
  pure (tableDescription known.owner slot.name table rows, location)

/-- Emit the information of the table names of the statements. The statements and contexts pair
by position; a statement without a context gets nothing. A place whose bytes the source cannot map
exactly gets nothing ({name}`SqlEditorSource.identifier?`). -/
def emitSqlEditorInfo (source : SqlEditorSource) (items : List (Located Syntax.Statement))
    (known : KnownDatabase) (contexts : List StatementContext) : TermElabM Unit := do
  let file ← getFileMap
  let bytes := source.text.toUTF8
  let mut replaced : List (List UInt8) := []
  for (item, context) in items.zip contexts do
    for slot in tableSlotsOf bytes item do
      let name := toString slot.name
      if let some (description, location?) := slotInformation known replaced context slot then
        if let some identifier := source.identifier? file slot.start slot.stop (Name.mkSimple name) then
          addSqlTableInfo identifier name description location?
    replaced := replaced ++ ((replacedTable? item.value).map (·.folded)).toList

end Belay.Sqlite
