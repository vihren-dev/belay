import Belay.Sqlite.Model.Programs.StatementRunLaws.ScriptRunValid
import Belay.Sqlite.Model.Programs.StatementRunLaws.AdmittedAtomsCounterExamples
import Belay.Sqlite.Model.Schema.Columns.AdmittedRunsExamples

set_option doc.verso true

/-! Examples of the run theorems of the Admitted atoms (ADR 0022, slice 4, part 3), each checked by the
kernel: the corollary {lit}`runScriptAllFrom_valid` applied to a script with CREATE INDEX, ADD COLUMN, DROP TABLE
of a table with an index and a trigger, a DELETE that cascades and a ROLLBACK, with no hypothesis on the
statements; the facts of the resolver on concrete statements; the conditions that stay in the theorems of
{lit}`runSqlFrom` and {lit}`runSql`, each with a run that breaks the atom when the condition fails. -/

namespace Belay.Sqlite.Model.AdmittedRunsExamples

open Belay.Sqlite.Model Syntax
open Belay.Sqlite.Model.ForeignKeyExamples (keysOn deleteOne)

/-- A new connection with foreign keys on. -/
def start : Connection := { state := { database := {} }, foreignKeys := true }

/-- The run of {name}`mixedSyntax` from {name}`start`, without values and without a clock. -/
def mixedRun : ScriptRun := runScriptFrom mixedContext none 0 start (bindValues mixedSyntax [])

/-- Whether an output is an error or the end of the run. -/
def Output.failed : Output → Bool
  | .error _ | .unmodeled _ => true
  | .rows _ | .done _ | .oneOf _ => false

-- The run gives 13 outputs and none fails. It ends with the five objects of the catalog (the tables `p`, `c`
-- and `t`, the index and the trigger), because ROLLBACK restores the table `t` that DROP TABLE dropped, and
-- no transaction is open.
#guard mixedRun.outputs.length == 13 && !mixedRun.outputs.any Output.failed &&
  mixedRun.connection.state.database.catalog.length == 5 && mixedRun.connection.state.snapshot.isNone

/-- The corollary applied to {name}`mixedSyntax`: the database of every complete execution of the script is
valid, and so is the snapshot when a transaction is open. The proof has no fact about CREATE INDEX, ADD COLUMN, DROP TABLE, the cascade or
ROLLBACK: the theorem needs only the start state, the mode and the limits. -/
theorem mixedRun_valid :
    ∀ run ∈ runScriptAllFrom mixedContext none 0 start (bindValues mixedSyntax []),
      run.connection.state.Holds (Database.Valid keysOn) :=
  runScriptAllFrom_valid mixedContext none 0 (bindValues mixedSyntax []) rfl rfl
    ⟨Database.valid_empty keysOn, fun _ same => nomatch same⟩

/-- The theorem of "rows aliased" applied to {name}`mixedSyntax`: the database of every complete execution of the
script satisfies {name}`Database.RowsAliased` and has a valid catalog under the limits of the profile, and so does the snapshot
when a transaction is open. The theorem has no hypothesis on the statements either. -/
theorem mixedRun_rowsAliased :
    ∀ run ∈ runScriptAllFrom mixedContext none 0 start (bindValues mixedSyntax []),
      run.connection.state.Holds (Database.RowsAliasedSupported keysOn.limits) :=
  runScriptAllFrom_holds_derived (rowsAliased_statementKeeps keysOn.limits) mixedContext none
    (fun _ _ _ _ keep _ _ _ ok _ ready =>
      ⟨resolveStatement_appliedValid mixedContext rfl rfl (keep.mono fun _ holds => holds.2) ok,
        (Bool.and_eq_true_iff.mp ready).1⟩)
    0 (bindValues mixedSyntax [])
    ⟨⟨(Database.valid_empty keysOn).admitted.rowsAliased, (Database.valid_empty keysOn).admitted.catalogSupported⟩, fun _ same => nomatch same⟩

end Belay.Sqlite.Model.AdmittedRunsExamples
