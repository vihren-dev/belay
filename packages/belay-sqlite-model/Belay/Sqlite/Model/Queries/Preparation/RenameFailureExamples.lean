import Belay.Sqlite.Model.Queries.Preparation.RenameCatalogExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.RenameFailureExamples

open Belay.Sqlite.Model Syntax

/-- {lit}`JOIN u ON 1`. -/
def joinU : Join where
  operator := []
  source := { table := name! "u", alias := none }
  condition := some (.numeric "1")
  usingColumns := none

-- SQLite reports the errors of dependent objects while the statement runs, and every other prepare error in prepare.
#guard (PrepareError.dependentObject .view (name! "v") .current (.expression (.noSuchColumn (name! "zz")))).reportedWhileRunning
#guard !(PrepareError.noSuchTable (name! "t")).reportedWhileRunning
#guard !(PrepareError.renameTargetTaken (name! "t")).reportedWhileRunning

end Belay.Sqlite.Model.Resolution.RenameFailureExamples
