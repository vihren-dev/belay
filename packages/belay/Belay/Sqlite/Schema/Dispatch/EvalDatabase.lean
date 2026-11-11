import Lean.Elab.SyntheticMVars
import Lean.Meta.Eval
import Belay.Sqlite.Schema.Rows.Database

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term Meta

/-- A database term that Lean evaluated while the file elaborates: the closed term and its value.
The editor reads the origin of the tables from the term ({lit}`originsOf`). -/
structure EvaluatedDatabase where
  /-- The closed term of the database after the elaboration. -/
  term : Expr
  /-- The value of the term. -/
  value : Database

end Belay.Sqlite
