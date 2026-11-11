import Lean.Elab.DocString
import Belay.Sqlite.Values.DateTime.Env

set_option doc.verso true

namespace Belay.Sqlite.SqlDoc

open Lean Elab Term Meta Belay.Sqlite

/-- The name in a header argument that must be a definition, or an error at the argument. -/
def definitionName (option : String) (argument : Doc.DocArg) : TermElabM Syntax :=
  match argument with
  | .ident name => pure name
  | other => throwErrorAt other.syntax
      m!"the header option {option} takes the name of a closed definition; write ({option} := name)"

end Belay.Sqlite.SqlDoc
