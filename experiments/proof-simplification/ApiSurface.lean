import Belay.Sqlite.Model.ScriptRunConstraints
import Belay.Sqlite.Model.ForeignKeyRuns
import Belay.Sqlite.Model.ScriptRunAdmittedRows

set_option doc.verso true

/-! Surface-run formulas derived without the corresponding per-atom endpoints.
Resolution supplies the admitted-run conditions; FK conditions remain explicit. -/

namespace Belay.Sqlite.Model.ProofSimplification

/-- For every execution context with the profile's limits, clock, index,
connection and surface script, initial admission on both stores implies final
admission. There is no premise on the script. Proof sketch: the resolver gives
{name}`Resolved.Statement.AppliedValid`; {name}`runScriptFrom_holds_derived`
lifts {name}`admitted_statementKeeps`. -/
theorem scriptAdmitted {profile : Profile} (context : ResolveContext)
    (clock : Option Clock) (index : Nat) {connection : Connection}
    (script : List (Syntax.Statement × List Value)) (execution : context.mode = .execution)
    (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.Admitted profile)) :
    (runScriptFrom context clock index connection script).connection.state.Holds
      (Database.Admitted profile) :=
  runScriptFrom_holds_derived (admitted_statementKeeps profile) context clock
    (fun _ _ _ _ keep ok => resolveStatement_appliedValid context execution same
      (keep.mono (fun _ admitted => admitted.catalogSupported)) ok) index script holds

/-- For every execution context with matching limits, clock, index, connection
and surface script, admission together with NOT NULL on both entry stores
survives. The script needs no extra premise. Proof sketch: specialize
{name}`runScriptFrom_admittedWith`; admission supplies ADD COLUMN row width. -/
theorem scriptNotNull {profile : Profile} (context : ResolveContext) (clock : Option Clock)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.AdmittedWith profile Database.NotNull)) :
    (runScriptFrom context clock index connection script).connection.state.Holds
      (Database.AdmittedWith profile Database.NotNull) :=
  runScriptFrom_admittedWith notNull_statementKeeps
    (fun _ statement admitted _ _ => statement.notNullCondition_of_admitted admitted)
    context clock index script execution same holds

/-- For every execution context with matching limits, clock, index, connection
and surface script, admission and type fitting on both stores survive. The
script needs no extra premise. Proof sketch: use
{name}`runScriptFrom_admittedWith`; the schema link provides the default fit. -/
theorem scriptTypesFit {profile : Profile} (context : ResolveContext) (clock : Option Clock)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.AdmittedWith profile Database.TypesFit)) :
    (runScriptFrom context clock index connection script).connection.state.Holds
      (Database.AdmittedWith profile Database.TypesFit) :=
  runScriptFrom_admittedWith typesFit_statementKeeps
    (fun _ statement admitted _ link => statement.typesFitCondition_of_link admitted link)
    context clock index script execution same holds

/-- For every execution context with matching limits, clock, index, connection
and surface script, admission and CHECK validity on both stores survive. The
script needs no extra premise. Proof sketch: specialize
{name}`runScriptFrom_admittedWith`; admission supplies width and CHECK bounds. -/
theorem scriptChecksHold {profile : Profile} (context : ResolveContext) (clock : Option Clock)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.AdmittedWith profile Database.ChecksHold)) :
    (runScriptFrom context clock index connection script).connection.state.Holds
      (Database.AdmittedWith profile Database.ChecksHold) :=
  runScriptFrom_admittedWith checksHold_statementKeeps
    (fun _ statement admitted _ _ => statement.checksHoldCondition_of_admitted admitted)
    context clock index script execution same holds

/-- For every profile, context, clock, index, connection and script, selected
row references survive on both stores if they hold initially and each reached
resolved statement meets its FK row condition. Failed resolution and halted
suffixes add no condition. Proof sketch: specialize {name}`runScriptFrom_holds`
with {name}`rowReferences_statementKeeps`, retaining the explicit conditions. -/
theorem scriptRowReferences (profile : Profile) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) {connection : Connection}
    (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds (fun database =>
      database.RowReferencesHold database.catalog.foreignKeyMapping))
    (conditions : ScriptConditionsWith (fun statement database =>
      statement.ForeignKeyRowsCondition profile database) context clock index connection script) :
    (runScriptFrom context clock index connection script).connection.state.Holds
      (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  runScriptFrom_holds (rowReferences_statementKeeps profile)
    context clock index script holds conditions

#print axioms scriptAdmitted
#print axioms scriptNotNull
#print axioms scriptTypesFit
#print axioms scriptChecksHold
#print axioms scriptRowReferences

-- These type comparisons check the frozen endpoint formulas. The named
-- experiment proofs above use only generic lifting and preservation evidence.
example : @scriptAdmitted = @runScriptFrom_admitted := rfl
example : @scriptNotNull = @runScriptFrom_notNull := rfl
example : @scriptTypesFit = @runScriptFrom_typesFit := rfl
example : @scriptChecksHold = @runScriptFrom_checksHold := rfl
example : @scriptRowReferences = @runScriptFrom_rowReferences := rfl

end Belay.Sqlite.Model.ProofSimplification
