import Belay.Sqlite.Model.AtomsConditionsOfLink
import Belay.Sqlite.Model.KeysUniqueRuns
import Belay.Sqlite.Model.ScriptRunApplied
import Belay.Sqlite.Model.ScriptRunDerived
import Belay.Sqlite.Model.ValidAtomsRuns
import Belay.Sqlite.Model.ValidAtomsTogether

set_option doc.verso true

/-! A generic surface run law for an admitted database with an additional invariant.
A caller supplies preservation evidence and derives its condition from admission and
the resolver's applied-catalog and schema-link facts. -/

namespace Belay.Sqlite.Model

/-- For the given profile and property of databases: the database is admitted under the profile
({name}`Database.Admitted`) and has the property. It is the invariant of the run theorems of
{lit}`runScriptAllFrom` for the atoms of slices 2 and 3. -/
abbrev Database.AdmittedWith (profile : Profile) (property : Database → Prop) (database : Database) : Prop :=
  database.Admitted profile ∧ property database

/-- The run theorem of {name}`runScriptAllFrom` for an atom of slices 2 and 3, for every statement theorem and
every way to give its condition. For every profile, atom and condition: if the statement theorem holds
({name}`StatementKeeps`), and for every clock, counters and parameters an admitted database gives the condition for each statement whose applied
catalog is valid, whose raw run is ready, and that meets {name}`Resolved.Statement.SchemaLink`, then for every context in execution mode with
the limits of the profile, clock, index, connection and statements with their values: if the state of the
connection satisfies {name}`SqlState.Holds` for {name}`Database.AdmittedWith` the atom, the state of the
connection of every complete execution of the script satisfies it. Proof sketch: {name}`runScriptAllFrom_holds_derived` for the conjunction of
{name}`admitted_statementKeeps` and the statement theorem of the atom; the resolver gives the validity of the
catalog after the statement ({name}`resolveStatement_appliedValid`) and the link
({name}`resolveStatement_certificate`). -/
theorem runScriptAllFrom_admittedWith {profile : Profile} {atom : Database → Prop}
    {condition : StatementCondition} (keeps : StatementKeeps atom condition)
    (derive : ∀ (value : Int) (counters : Counters) (parameters : List Value)
      (database : Database) (statement : Resolved.Statement), database.Admitted profile →
      statement.AppliedValid profile.limits database → statement.SchemaLink database.catalog →
        (runStatement value counters parameters statement database).ready = true →
        condition value counters parameters statement database)
    (context : ResolveContext) (clock : Option Clock) (index : Nat) {connection : Connection}
    (script : List (Syntax.Statement × List Value)) (execution : context.mode = .execution)
    (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.AdmittedWith profile atom)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds (Database.AdmittedWith profile atom) :=
  runScriptAllFrom_holds_derived ((admitted_statementKeeps profile).and keeps) context clock
    (fun _ _ _ _ keep _ _ _ ok _ ready =>
      have applied := resolveStatement_appliedValid context execution same (keep.mono fun _ h => h.1.catalogSupported) ok
      ⟨⟨applied, (Bool.and_eq_true_iff.mp ready).1⟩, derive _ _ _ _ _ keep.1.1 applied
        ((resolveStatement_certificate context _ _ _ _ ok).link profile.limits (same ▸ keep.1.1.catalogSupported))
        (Bool.and_eq_true_iff.mp ready).1⟩) index script holds

end Belay.Sqlite.Model
