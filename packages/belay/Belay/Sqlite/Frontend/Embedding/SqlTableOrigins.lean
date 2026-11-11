import Belay.Sqlite.Frontend.Embedding.SqlTableSlots
import Belay.Sqlite.Frontend.Embedding.SqlEditorSource
import Lean.Elab.DeclarationRange
import Lean.Elab.Term

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term Belay.Sqlite.Model

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

/-- The longest chain of constants that stand for each other ({lit}`def c := b`, {lit}`def b := a`)
that {lit}`originsOf` follows from the database term to a {lit}`db!` declaration. A chain that is
longer gives no origin, so the table names of that database get no jump. -/
def aliasChainLimit : Nat := 64

end Belay.Sqlite
