import Belay.Sqlite.Schema.Columns.SqlStatementContexts
import Belay.Sqlite.Schema.Dispatch.SqlTableOrigins
import Belay.Sqlite.Queries.Preparation.SqlNameInfo
import Belay.Sqlite.Frontend.Embedding.SqlEditorInfo

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term Belay.Sqlite.Model

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

end Belay.Sqlite
