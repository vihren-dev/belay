import Belay.Sqlite.Model.ValidAtomsRuns
import Belay.Sqlite.Model.AdmittedStatementKeeps
import Belay.Sqlite.Model.ForeignKeyRuns
import Belay.Sqlite.Model.AdmittedSqlRunsRows

set_option doc.verso true

/-! Exact resolved-run claims obtained from generic lifting. These declarations
are experiments, not replacement public endpoints. -/

namespace Belay.Sqlite.Model.ProofSimplification

/-- For every position, script and state, NOT NULL on the current database and
saved snapshot survives the run when each reached statement meets its NOT NULL
condition. The condition requires nothing after a halt. Proof sketch: apply
{name}`runSqlFrom_holds` to {name}`notNull_statementKeeps`. -/
theorem sqlFromNotNull (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds Database.NotNull)
    (conditions : NotNullRunConditions position script state) :
    (runSqlFrom position script state).Holds Database.NotNull :=
  runSqlFrom_holds notNull_statementKeeps position script holds conditions

/-- For every fresh script and database, the type-fitting atom survives the run
when it holds initially and each reached statement meets its type-fitting
condition. Proof sketch: apply {name}`runSql_holds` to
{name}`typesFit_statementKeeps`; no readiness premise is added. -/
theorem sqlTypesFit (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : Database.TypesFit database) (conditions : TypesFitRunConditions 0 script { database }) :
    (runSql script database).Holds Database.TypesFit :=
  runSql_holds typesFit_statementKeeps script holds conditions

/-- For every position, script and state, the CHECK atom on both entry stores
survives when each reached statement meets its CHECK condition. The outcome
includes the visible and persisted databases of a pending transaction. Proof
sketch: apply {name}`runSqlFrom_holds` to {name}`checksHold_statementKeeps`. -/
theorem sqlFromChecksHold (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds Database.ChecksHold)
    (conditions : ChecksHoldRunConditions position script state) :
    (runSqlFrom position script state).Holds Database.ChecksHold :=
  runSqlFrom_holds checksHold_statementKeeps position script holds conditions

/-- For every position, script and state, wide rows on the current database and
snapshot survive when each reached statement passes the support check. No
extra invariant is assumed. Proof sketch: apply {name}`runSqlFrom_holds_ready`
to {name}`rowsWide_statementKeeps` with its always-true extra condition. -/
theorem sqlFromRowsWide (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds Database.RowsWide)
    (supported : supportedSqlFrom position script state = true) :
    (runSqlFrom position script state).Holds Database.RowsWide :=
  runSqlFrom_holds_ready rowsWide_statementKeeps position script holds supported
    (RunConditionsWith.always _ _ _)

/-- For every profile and fresh script, admission survives if it holds initially,
all reached statements pass support, and each reached statement leaves a valid
catalog. Proof sketch: use {name}`admitted_statementKeeps` with
{name}`runSql_holds_ready`, retaining both original run premises. -/
theorem sqlAdmitted {profile : Profile} (script : List (Resolved.Statement × List Value))
    {database : Database} (holds : Database.Admitted profile database)
    (supported : supportedSqlFrom 0 script { database } = true)
    (conditions : RunConditionsWith (Resolved.Statement.AppliedValid profile.limits)
      0 script { database }) :
    (runSql script database).Holds (Database.Admitted profile) :=
  runSql_holds_ready (admitted_statementKeeps profile) script holds supported conditions

/-- For every profile, fixed mapping, position, script and state, compatibility
and row references survive on every retained database if they hold on both
entry stores and each reached statement keeps the parent schema and meets its
row condition. Proof sketch: lift {name}`foreignKeyAtoms_statementKeeps` with
{name}`runSqlFrom_holds`; no selected-mapping substitution removes a premise. -/
theorem sqlFromForeignKeyAtoms (profile : Profile) (mapping : ForeignKeyMapping)
    (position : Nat) (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds (fun database =>
      database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping))
    (conditions : RunConditionsWith (fun statement database =>
      statement.KeepsParentSchema ∧ statement.ForeignKeyRowsCondition profile database)
      position script state) :
    (runSqlFrom position script state).Holds (fun database =>
      database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping) :=
  runSqlFrom_holds (foreignKeyAtoms_statementKeeps profile mapping)
    position script holds conditions

#print axioms sqlFromNotNull
#print axioms sqlTypesFit
#print axioms sqlFromChecksHold
#print axioms sqlFromRowsWide
#print axioms sqlAdmitted
#print axioms sqlFromForeignKeyAtoms

-- The comparison terms require exactly the old theorem types. Proof
-- irrelevance then proves equality; none of the named proofs uses an endpoint.
example : @sqlFromNotNull = @runSqlFrom_notNull := rfl
example : @sqlTypesFit = @runSql_typesFit := rfl
example : @sqlFromChecksHold = @runSqlFrom_checksHold := rfl
example : @sqlFromRowsWide = @runSqlFrom_rowsWide := rfl
example : @sqlAdmitted = @runSql_admitted := rfl
example : @sqlFromForeignKeyAtoms = @runSqlFrom_foreignKeyAtoms := rfl

end Belay.Sqlite.Model.ProofSimplification
