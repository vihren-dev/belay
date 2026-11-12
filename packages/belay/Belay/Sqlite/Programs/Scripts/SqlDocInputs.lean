import Belay.Sqlite.Frontend.Embedding.SqlDocClosed
import Belay.Sqlite.Programs.Scripts.SqlDocClosed
import Belay.Sqlite.Frontend.Embedding.SqlDocHeader
import Belay.Sqlite.Frontend.Embedding.SqlDocReport

set_option doc.verso true

namespace Belay.Sqlite.SqlDoc

open Lean Elab Term Belay.Sqlite

/-- The evaluated closed inputs of a block. -/
structure Inputs where
  /-- The database that every run of the block starts from. -/
  database : Database
  /-- The clock and counters of the run; {name}`Env.default` when the header gives none. -/
  environment : Env
  /-- The complete typed observation from {lit}`(expected := name)`, if the header gives one. -/
  typedOutputs : Option (List Output)
  /-- The values of each statement from {lit}`(values := name)`, if the header gives them. -/
  explicitValues : Option (List (List Belay.Sqlite.Model.Value))

end Belay.Sqlite.SqlDoc
