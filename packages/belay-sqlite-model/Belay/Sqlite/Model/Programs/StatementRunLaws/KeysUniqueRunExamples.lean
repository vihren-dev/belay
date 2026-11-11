import Belay.Sqlite.Model.Programs.StatementRunLaws.KeysUniqueRuns
import Belay.Sqlite.Model.Schema.Columns.KeysUniqueRunExamples

set_option doc.verso true

/-! Examples of the run theorem of the atom "keys unique" (ADR 0022, slice 2), each checked by the
kernel: the theorem applied to a resolved script with an INSERT, an upsert, a DELETE that
cascades and a ROLLBACK, and finding 1 of the keys-unique status file as a run whose outcome
breaks the atom without the run conditions. -/

namespace Belay.Sqlite.Model.KeysUniqueRunExamples

open Belay.Sqlite.Model

open Belay.Sqlite.Model.KeysUniqueExamples (tableOnly filterPastWidthIndex columnFive)

/-- The run theorem applied to {name}`cascadeScript`: each database of the outcome of
{name}`runSql` from the empty database satisfies {name}`Database.KeysUnique`. The script has no
CREATE INDEX, ADD COLUMN or DROP, so it meets {name}`RunConditionsWith` for {name}`Resolved.Statement.RunCondition`
({name}`RunConditionsWith.of_unconditioned`). -/
theorem cascadeScript_keysUnique : (runSql cascadeScript {}).Holds Database.KeysUnique :=
  runSql_holds keysUnique_statementKeeps cascadeScript (by decide +kernel)
    (RunConditionsWith.of_unconditioned (fun _ _ _ _ _ => Resolved.Statement.runCondition_of_unconditioned)
      _ _ _ (by decide +kernel))

-- The start database keeps the keys unique, and the outcome of the run does not: the run
-- theorem of `runSql` needs its run conditions (the CREATE INDEX does not meet its condition).
example : tableOnly.KeysUnique ∧ ¬(runSql findingScript tableOnly).Holds Database.KeysUnique := by decide +kernel

end Belay.Sqlite.Model.KeysUniqueRunExamples
