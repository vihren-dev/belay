import Belay.Sqlite.Frontend.Embedding.DbBang
import Belay.Sqlite.Schema.Rows.DbBang

set_option doc.verso true

namespace Belay.Sqlite.Check

open Lean Meta Elab Term

/-- A database exists: the empty one. Compiled evaluation needs it for its result type. -/
instance : Nonempty Database := ⟨Database.empty⟩

/-- Raw database data exists: the data of the empty database. -/
instance : Nonempty Database.Raw := ⟨Database.empty.raw⟩

end Belay.Sqlite.Check
