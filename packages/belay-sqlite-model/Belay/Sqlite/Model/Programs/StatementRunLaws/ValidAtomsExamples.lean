import Belay.Sqlite.Model.Programs.StatementRunLaws.ValidAtomsTogether
import Belay.Sqlite.Model.Programs.StatementRunLaws.ValidAtomsRuns
import Belay.Sqlite.Model.Schema.Columns.ValidAtomsExamples

set_option doc.verso true

/-! Examples of the run theorems of the atoms "not null", "types fit", "checks hold" and of the four
atoms together (ADR 0022, slice 3), each checked by the kernel: the corollary applied to a resolved
script with a CHECK, a NOT NULL column, a STRICT table, an upsert, a cascading DELETE and a
ROLLBACK, and the SET NULL action of a foreign key that writes NULL into a NOT NULL column of the
child. The counterexamples of the conditions of ADD COLUMN are in {lit}`RowLocalExamples`. -/

namespace Belay.Sqlite.Model.ValidAtomsExamples

open Belay.Sqlite.Model

open Belay.Sqlite.Model.ForeignKeyExamples renaming name → written

/-- The corollary applied to {name}`strictCascadeScript`: each database of the outcome of
{name}`runSql` from the empty database satisfies {name}`Database.ConstraintAtoms`. The script has no
CREATE INDEX, ADD COLUMN or DROP, so it meets {name}`RunConditionsWith` for {name}`Resolved.Statement.AtomsCondition`
({name}`RunConditionsWith.of_unconditioned` with
{name}`Resolved.Statement.atomsCondition_of_unconditioned`). -/
theorem strictCascadeScript_constraintAtoms : (runSql strictCascadeScript {}).Holds Database.ConstraintAtoms :=
  runSql_holds constraintAtoms_statementKeeps strictCascadeScript
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (RunConditionsWith.of_unconditioned (unconditioned := Resolved.Statement.unconditioned)
      (fun _ _ _ _ _ => Resolved.Statement.atomsCondition_of_unconditioned) _ _ _
      (by decide +kernel))

/-- The run theorem of "not null" applied to {name}`setNullScript`: the database that the failed
run keeps satisfies {name}`Database.NotNull`, because the write of NULL fails before it is stored. -/
theorem setNullScript_notNull : (runSql setNullScript {}).Holds Database.NotNull :=
  runSql_holds notNull_statementKeeps setNullScript (by decide +kernel)
    (RunConditionsWith.of_unconditioned (unconditioned := Resolved.Statement.unconditioned)
      (fun _ _ _ _ _ unconditioned => (Resolved.Statement.atomsCondition_of_unconditioned unconditioned).2.1) _ _ _
      (by decide +kernel))

end Belay.Sqlite.Model.ValidAtomsExamples
