import Belay.Sqlite.Model.Programs.StatementRunLaws.ScriptRunValid
import Belay.Sqlite.Model.Programs.StatementRunLaws.AdmittedAtomsCounterExamples
import Belay.Sqlite.Model.Schema.Ddl.AdmittedRunsConditionExamples

set_option doc.verso true

/-! Examples of the pieces of the run theorems of the Admitted atoms (ADR 0022, slice 4, part 3), each checked
by the kernel: the facts of the resolver on concrete statements ({lit}`Resolved.Statement.SchemaLink`), the
definitions of the invariants, the theorems of {lit}`runSql` applied to a script, and the conditions that
stay in the theorems of {lit}`runSqlFrom` and {lit}`runSql`, each with a run that breaks the atom when the
condition fails. -/

namespace Belay.Sqlite.Model.AdmittedRunsConditionExamples

open Belay.Sqlite.Model

open Belay.Sqlite.Model.AdmittedAtomsEngineExamples (emptyDatabase)
open Belay.Sqlite.Model.AdmittedAtomsCounterExamples (oneTable largestRowidTable insertCells)

-- The theorem of `runSql` applied: one INSERT into `emptyDatabase` keeps "rows shaped".
-- This invariant needs neither readiness nor a condition on the statement.
example : (runSql [(.insert 0 [[.value (.integer 1), .value (.text [97])]] [], [])] emptyDatabase).Holds
    Database.RowsShaped :=
  runSql_holds rowsShaped_statementKeeps _ AdmittedAtomsEngineExamples.emptyDatabase_shaped
    (RunConditionsWith.always _ _ _)

example : supportedSqlFrom 0 pastLargest { database := oneTable largestRowidTable } = false := by decide +kernel

end Belay.Sqlite.Model.AdmittedRunsConditionExamples
